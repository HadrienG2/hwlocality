//! Looking for I/O objects

use crate::{
    errors::ParameterError,
    object::{
        attributes::{ObjectAttributes, PCIDomain},
        depth::Depth,
        TopologyObject,
    },
    topology::Topology,
};
#[allow(unused)]
#[cfg(test)]
use similar_asserts::assert_eq;
use std::iter::FusedIterator;

/// # Finding I/O objects
//
// --- Implementation details ---
//
// Inspired by https://hwloc.readthedocs.io/en/stable/group__hwlocality__advanced__io.html
// but inline functions had to be reimplemented in Rust. Further, queries
// pertaining to ancestors and children were moved to the corresponding sections.
impl Topology {
    /// Enumerate PCI devices in the system
    #[doc(alias = "hwloc_get_next_pcidev")]
    pub fn pci_devices(
        &self,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    {
        self.objects_at_depth(Depth::PCIDevice)
    }

    /// Find the PCI device object matching the PCI bus id given domain, bus
    /// device and function PCI bus id
    #[doc(alias = "hwloc_get_pcidev_by_busid")]
    pub fn pci_device_by_bus_id(
        &self,
        domain: PCIDomain,
        bus_id: u8,
        bus_device: u8,
        function: u8,
    ) -> Option<&TopologyObject> {
        self.pci_devices().find(|obj| {
            let Some(ObjectAttributes::PCIDevice(pci)) = obj.attributes() else {
                #[cfg(not(tarpaulin_include))]
                unreachable!("All PCI devices should have PCI attributes")
            };
            pci.domain() == domain
                && pci.bus_id() == bus_id
                && pci.bus_device() == bus_device
                && pci.function() == function
        })
    }

    /// Find the PCI device object matching the PCI bus id given as a string
    /// of format "xxxx:yy:zz.t" (with domain) or "yy:zz.t" (without domain)
    ///
    /// # Errors
    ///
    /// - [`ParameterError`] if the given string does not match the PCI bus id
    ///   format given above
    #[doc(alias = "hwloc_get_pcidev_by_busidstring")]
    pub fn pci_device_by_bus_id_string(
        &self,
        bus_id: &str,
    ) -> Result<Option<&TopologyObject>, ParameterError<String>> {
        // Package `bus_id` into an error if need be
        let make_error = || ParameterError(bus_id.to_owned());

        // Assume well-formatted string
        let parse_domain = |s| PCIDomain::from_str_radix(s, 16).map_err(|_| make_error());
        let parse_u8 = |s| u8::from_str_radix(s, 16).map_err(|_| make_error());

        // Extract initial hex (whose semantics are ambiguous at this stage)
        let (int1, mut rest) = bus_id.split_once(':').ok_or_else(make_error)?;

        // From presence/absence of second ':', deduce if int1 was a domain or
        // a bus id in the default 0 domain.
        let (domain, bus) = if let Some((bus, next_rest)) = rest.split_once(':') {
            rest = next_rest;
            (parse_domain(int1)?, parse_u8(bus)?)
        } else {
            (0, parse_u8(int1)?)
        };

        // Parse device and function IDs, and forward to non-textual lookup
        let (dev, func) = rest.split_once('.').ok_or_else(make_error)?;
        Ok(self.pci_device_by_bus_id(domain, bus, parse_u8(dev)?, parse_u8(func)?))
    }

    /// Enumerate OS devices in the system
    #[doc(alias = "hwloc_get_next_osdev")]
    pub fn os_devices(
        &self,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    {
        self.objects_at_depth(Depth::OSDevice)
    }

    /// Enumerate bridges in the system
    #[doc(alias = "hwloc_get_next_bridge")]
    pub fn bridges(
        &self,
    ) -> impl DoubleEndedIterator<Item = &TopologyObject> + Clone + ExactSizeIterator + FusedIterator
    {
        self.objects_at_depth(Depth::Bridge)
    }
}

#[allow(clippy::cognitive_complexity)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        object::{lists::tests::compare_object_sets, types::ObjectType},
        strategies::any_string,
    };
    use proptest::prelude::*;
    use similar_asserts::assert_eq;
    use std::{collections::HashMap, ptr, sync::OnceLock};

    // --- Enumerate I/O devices ---

    #[test]
    fn io_object_lists() -> Result<(), TestCaseError> {
        let topology = Topology::test_instance();
        compare_object_sets(
            topology.pci_devices(),
            topology.objects_with_type(ObjectType::PCIDevice),
        )?;
        compare_object_sets(
            topology.os_devices(),
            topology.objects_with_type(ObjectType::OSDevice),
        )?;
        compare_object_sets(
            topology.bridges(),
            topology.objects_with_type(ObjectType::Bridge),
        )?;
        Ok(())
    }

    // --- Find PCI devices by address ---

    /// PCI device address
    #[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
    struct PCIAddress {
        domain: PCIDomain,
        bus_id: u8,
        bus_device: u8,
        function: u8,
    }
    //
    impl PCIAddress {
        /// Turn this address into its standard string form
        ///
        /// You may only cut out the domain part by setting `with_domain` to
        /// false when `domain` is zero.
        fn stringify(self, with_domain: bool) -> String {
            if with_domain {
                format!(
                    "{:04x}:{:02x}:{:02x}.{:02x}",
                    self.domain, self.bus_id, self.bus_device, self.function
                )
            } else {
                assert_eq!(self.domain, 0);
                format!(
                    "{:02x}:{:02x}.{:02x}",
                    self.bus_id, self.bus_device, self.function
                )
            }
        }
    }
    //
    impl Arbitrary for PCIAddress {
        type Parameters = <(PCIDomain, [u8; 3]) as Arbitrary>::Parameters;
        type Strategy = prop::strategy::Map<
            <(PCIDomain, [u8; 3]) as Arbitrary>::Strategy,
            fn((PCIDomain, [u8; 3])) -> Self,
        >;

        fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
            <(PCIDomain, [u8; 3]) as Arbitrary>::arbitrary_with(args).prop_map(
                |(domain, [bus_id, bus_device, function])| Self {
                    domain,
                    bus_id,
                    bus_device,
                    function,
                },
            )
        }
    }

    /// List of PCI devices keyed by address
    fn pci_devices_by_address() -> &'static HashMap<PCIAddress, &'static TopologyObject> {
        static RESULT: OnceLock<HashMap<PCIAddress, &'static TopologyObject>> = OnceLock::new();
        RESULT.get_or_init(|| {
            let mut result = HashMap::new();
            for device in Topology::test_instance().pci_devices() {
                let Some(ObjectAttributes::PCIDevice(pci)) = device.attributes() else {
                    unreachable!("All PCI devices should have PCI attributes")
                };
                assert!(result
                    .insert(
                        PCIAddress {
                            domain: pci.domain(),
                            bus_id: pci.bus_id(),
                            bus_device: pci.bus_device(),
                            function: pci.function(),
                        },
                        device
                    )
                    .is_none());
            }
            result
        })
    }

    /// Generate a PCI device address that is usually valid, but may not be
    fn pci_address() -> impl Strategy<Value = PCIAddress> {
        let valid_pci_addresses = pci_devices_by_address().keys().copied().collect::<Vec<_>>();
        if valid_pci_addresses.is_empty() {
            any::<PCIAddress>().boxed()
        } else {
            prop_oneof![
                4 => prop::sample::select(valid_pci_addresses),
                1 => any::<PCIAddress>(),
            ]
            .boxed()
        }
    }

    proptest! {
        /// Test for [`Topology::pci_device_by_bus_id()`]
        #[allow(clippy::option_if_let_else)]
        #[test]
        fn pci_device_by_bus_id(addr in pci_address()) {
            let topology = Topology::test_instance();
            let result = topology.pci_device_by_bus_id(
                addr.domain,
                addr.bus_id,
                addr.bus_device,
                addr.function,
            );
            if let Some(expected) = pci_devices_by_address().get(&addr) {
                assert!(ptr::eq(
                    result.unwrap(),
                    *expected
                ));
            } else {
                assert!(result.is_none());
            }
        }
    }

    /// List of PCI devices keyed by stringified address
    fn pci_devices_by_address_string() -> &'static HashMap<String, &'static TopologyObject> {
        static RESULT: OnceLock<HashMap<String, &'static TopologyObject>> = OnceLock::new();
        RESULT.get_or_init(|| {
            let mut result = HashMap::new();
            for (address, device) in pci_devices_by_address() {
                assert!(result.insert(address.stringify(true), *device).is_none());
                if address.domain == 0 {
                    assert!(result.insert(address.stringify(false), *device).is_none());
                }
            }
            result
        })
    }

    /// Generate a string that may or may not be a PCI device address
    fn pci_address_string() -> impl Strategy<Value = String> {
        let valid_str_addresses = pci_devices_by_address_string()
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        fn push_short_addr(out: &mut String, chars: &[char]) {
            assert_eq!(chars.len(), 6);
            for &c in &chars[0..2] {
                out.push(c);
            }
            out.push(':');
            for &c in &chars[2..4] {
                out.push(c);
            }
            out.push('.');
            for &c in &chars[4..6] {
                out.push(c);
            }
        }
        let random_string = prop_oneof![
            // Same skeleton as a full address, but unlikely to be an address
            any::<[char; 10]>().prop_map(|chars| {
                let mut out = String::with_capacity(13);
                for &c in &chars[..4] {
                    out.push(c);
                }
                out.push(':');
                push_short_addr(&mut out, &chars[4..]);
                out
            }),
            // Same skeleton as a short address, but unlikely to be an address
            any::<[char; 6]>().prop_map(|chars| {
                let mut out = String::with_capacity(8);
                push_short_addr(&mut out, &chars[..]);
                out
            }),
            // Random textual junk
            any_string(),
        ];
        if valid_str_addresses.is_empty() {
            random_string.boxed()
        } else {
            prop_oneof![
                // Actually a PCI address, with or without the domain part
                3 => prop::sample::select(valid_str_addresses),
                // Random string that may or may not look like a PCI address
                2 => random_string,
            ]
            .boxed()
        }
    }

    proptest! {
        /// Test for [`Topology::pci_device_by_bus_id_string()`]
        #[allow(clippy::option_if_let_else)]
        #[test]
        fn pci_device_by_bus_id_string(addr in pci_address_string()) {
            let topology = Topology::test_instance();
            let result = topology.pci_device_by_bus_id_string(&addr);

            // Handle success case
            if let Some(expected) = pci_devices_by_address_string().get(&addr) {
                prop_assert!(ptr::eq(
                    result.unwrap().unwrap(),
                    *expected
                ));
                return Ok(());
            }

            // Determine if string at least matches expected format
            let is_hex = |s: &str| s.chars().all(|c| c.is_ascii_hexdigit());
            let is_valid_full =
                addr.len() == 13
                && addr.is_char_boundary(4) && is_hex(&addr[..4])
                && addr.is_char_boundary(5) && &addr[4..5] == ":"
                && addr.is_char_boundary(7) && is_hex(&addr[5..7])
                && addr.is_char_boundary(8) && &addr[7..8] == ":"
                && addr.is_char_boundary(10) && is_hex(&addr[8..10])
                && addr.is_char_boundary(11) && &addr[10..11] == "."
                && is_hex(&addr[11..]);
            let is_valid_short =
                addr.len() == 8
                && addr.is_char_boundary(2) && is_hex(&addr[..2])
                && addr.is_char_boundary(3) && &addr[2..3] == ":"
                && addr.is_char_boundary(5) && is_hex(&addr[3..5])
                && addr.is_char_boundary(6) && &addr[5..6] == "."
                && is_hex(&addr[6..]);
            if is_valid_full || is_valid_short {
                prop_assert!(matches!(result, Ok(None)));
            } else {
                prop_assert!(matches!(result, Err(e) if e == ParameterError::from(addr)));
            }
        }
    }
}
