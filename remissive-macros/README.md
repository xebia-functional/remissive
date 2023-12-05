This crate provides the `#[remissive]` and `#[remissive_target]` macros for use
with the `remissive` crate. These macros allow boilerplate-free creation of a
lexicon of protocol-specific message types, allowing the user to focus creative
energy on payloads rather than common ceremony (e.g., version negotiation) and
message framing.

### Examples

Here's an example of a protocol that inherits version negotiation and
acknowledgment from `remissive` and then defines three additional message types
of its own:

```rust
use remissive::*;
use remissive_macros::{remissive, remissive_target};
use serde::{Serialize, Deserialize};

#[remissive(Body, 0)]
#[derive(Debug, PartialEq)]
struct A;

#[remissive(Body, 1)]
#[derive(Debug, PartialEq)]
struct B(u32);

#[remissive(Body, 2)]
#[derive(Debug, PartialEq)]
struct C
{
	a: u64,
	b: f64
}

#[remissive_target]
#[derive(Debug, PartialEq)]
enum Body
{
	// Field definitions are filled in by the `remissive_target` macro. The
	// generated variants, in definition order, are:
	// * `ProposeVersion`
	// * `AcceptedVersion`
	// * `SupportedVersions`
	// * `Acknowledged`
	// * `A`
	// * `B`
	// * `C`
}

fn example() {
	let propose_version = Body::ProposeVersion(3.into());
	let accepted_version = Body::AcceptedVersion(AcceptedVersion);
	let supported_versions = Body::SupportedVersions(SupportedVersions {
		versions: [Some(2.into()), Some(1.into()), None, None]
	});
	let acknowledged = Body::Acknowledged(Acknowledged);
	let a = Body::A(A);
	let b = Body::B(B(42));
	let c = Body::C(C { a: 42, b: 3.14 });

	let message: Message<Body> = Message::with_id_and_body(0, propose_version);
	const N: usize = Message::<Body>::serial_buffer_size();
	let serialized = message.serialize::<N>().unwrap();
	let deserialized = Message::<Body>::deserialize(&serialized).unwrap();
	assert_eq!(message, deserialized);
}
```

Here's the example from the `Elementary Usage` section of the `remissive` crate
documentation, rewritten to use the `#[remissive]` and `#[remissive_target]`
macros:

```rust
use remissive::{HeaplessVec, Message};
use remissive_macros::{remissive, remissive_target};
use serde::{Serialize, Deserialize};

#[remissive(Body, 0)]
#[derive(PartialEq, Debug)]
struct ComputeRequest { a: u32, b: u32 }

#[remissive(Body, 1)]
#[derive(PartialEq, Debug)]
struct ComputeResponse { result: u32 }

#[remissive_target]
#[derive(PartialEq, Debug)]
enum Body {
	// Field definitions are filled in by the `remissive_target` macro. The
	// generated variants, in definition order, are:
	// * `ProposeVersion`
	// * `AcceptedVersion`
	// * `SupportedVersions`
	// * `Acknowledged`
	// * `ComputeRequest`
	// * `ComputeResponse`
}

type Msg = Message<Body>;
const N: usize = Msg::serial_buffer_size();

fn example() {
	// Hypothetical message to request a computation.
	let message = Msg::with_id_and_body(
		1, Body::ComputeRequest(ComputeRequest { a: 1, b: 2 }));
	let serialized: HeaplessVec<N> = message.serialize().unwrap();
	let deserialized = Msg::deserialize(&serialized).unwrap();
	assert_eq!(message, deserialized);

	// Hypothetical message to respond to a computation request.
	let message = Msg::with_id_and_body(
		1, Body::ComputeResponse(ComputeResponse { result: 3 }));
	let serialized: HeaplessVec<N> = message.serialize().unwrap();
	let deserialized = Msg::deserialize(&serialized).unwrap();
	assert_eq!(message, deserialized);
}
```
