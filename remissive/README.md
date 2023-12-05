Remissive defines an opinionated extensible skeletal message protocol that can
be used with both embedded and standard applications. It provides built-in
support for version negotiation, stateless acknowledgment, and compact binary
serialization (via [`postcard`](https://crates.io/crates/postcard)). Message
types are unified under a generic `Message` type whose parameter establishes the
complete scope of the message lexicon. Remissive is transport-neutral, so the
same message lexicon may be used over UART, UDP, TCP, WebSocket, etc., and
different message lexicons may be defined within the same application. The
Remissive API can be used manually, but using the
[`remissive_macros`](../remissive-macros) crate is recommended to further
streamline development and reduce boilerplate.

The name "Remissive" is a portmanteau of "missive" and quite a few other
possibilities, like "re-" (do again), "remit" (relief of pain), and "remiss"
(really ought to exist already). It's also a play on "remissive", in the sense
that it is both the sin of writing yet another message framework and also its
absolution. I've built probably two dozen message frameworks in half as many
languages already, and I would like to have a one-and-for-all framework in Rust.

# Elementary Usage

`Message` is the core type of Remissive. It is a generic `struct` wrapping a
_conversation identifier_ and a user-specified message type, called the _body_.

The conversation identifier represents a conversation between two parties. Each
conversation is identified by a 2-tuple of `<sender, id>`, where `sender` is the
party that initiated the conversation and `id` is a monotonically increasing
value that uniquely identifies the conversation for `sender`. A `Message`
carries only the `id` of the conversation, so the `sender` must be inferred from
the context of receipt. A party begins a conversation by allocating a new
conversation identifier, stamping it onto a request, and transmitting that
request to its partner. The partner receives the request, uses the same
conversation identifier to stamp its response, and transmits the response back
to the original party. This continues until the conversation is complete.
Completeness is determined by the message protocol itself, not by Remissive, and
likewise for other properties like in-order delivery, reliability, and
parallelism. This simple scheme allows users to specify and construct
arbitrarily complex message protocols.

The body is the payload of the message, its _raison d'être_. It can be any type
that implements the `Serialize` and `Deserialize` traits from
[`serde`](https://crates.io/crates/serde). This is where a user focuses their
efforts when implementing a message protocol.

Here's an example using variable-length text messages and heap-fixed-bound
serialization to be embedded-friendly:

```rust
use remissive::{HeaplessVec, Message};

type Msg = Message<String>;

fn example() {
	// Hypothetical message to request a computation.
	let message = Msg::with_id_and_body(1, "compute: 1 + 2".to_string());
	let serialized: HeaplessVec<50> = message.serialize().unwrap();
	let deserialized = Msg::deserialize(&serialized).unwrap();
	assert_eq!(message, deserialized);

	// Hypothetical message to respond to a computation request.
	let message = Msg::with_id_and_body(1, "result: 3".to_string());
	let serialized: HeaplessVec<50> = message.serialize().unwrap();
	let deserialized = Msg::deserialize(&serialized).unwrap();
	assert_eq!(message, deserialized);
}
```

This demonstrates that any data type can be used, but nontrivial protocols
usually use an `enum` type to define a precise, efficient message lexicon.
Here's a more realistic rendition of the above example, using fixed-bound
serialization to be embedded-friendly:

```rust
use remissive::{HeaplessVec, Message};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct ComputeRequest { a: u32, b: u32 }

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct ComputeResponse { result: u32 }

#[derive(Serialize, Deserialize, PartialEq, Debug)]
enum Body {
	ComputeRequest(ComputeRequest),
	ComputeResponse(ComputeResponse)
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

Use `Message::serialize_alloc` for dynamic serialization. This method is
available unless the `no-std` feature is enabled.

# Versioning

Remissive supports version negotiation by including three predefined messages:
`ProposeVersion`, `AcceptedVersion`, and `SupportedVersions`. Just include these
messages in your lexicon and use `ProposeVersion::negotiate` on the "server":

```rust
use remissive::*;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct ComputeRequest { a: u32, b: u32 }

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct ComputeResponse { result: u32 }

#[derive(Serialize, Deserialize, PartialEq, Debug)]
enum Body {
	ProposeVersion(ProposeVersion),
	AcceptedVersion(AcceptedVersion),
	SupportedVersions(SupportedVersions),
	ComputeRequest(ComputeRequest),
	ComputeResponse(ComputeResponse)
}

type Msg = Message<Body>;
const N: usize = Msg::serial_buffer_size();

fn example() {
	// The client wants version 3 of the protocol. In a real application, this
	// would be bundled into an `Msg`.
	let proposal: ProposeVersion = 3.into();

	// The server supports versions 2, 3, and 4 of the protocol, so negotiation
	// will produce an `AcceptedVersion` message with version 3.
	let accepted = proposal.negotiate(&[2.into(), 3.into(), 4.into()]).unwrap();
	assert_eq!(accepted, AcceptedVersion);

	// The server supports versions 1 and 2 of the protocol, so negotiation will
	// will produce a `SupportedVersions` message with these versions. The
	// client can then choose among the supported versions and propose one it
	// likes to the server.
	let rejected = proposal.negotiate(&[1.into(), 2.into()]).unwrap_err();
	assert_eq!(
		rejected,
		SupportedVersions {
			versions: [Some(2.into()), Some(1.into()), None, None]
		}
	);
}
```

# Features

The following Cargo features are available:

* `debug`: The `Debug` trait is implemented for `Message` iff it is implemented
  for its type parameter. This feature is enabled by default, but may be disabled
  to save space for embedded applications.
* `display`: The `Display` trait is implemented for `Message` iff it is
  implemented for its type parameter. This feature is enabled by default, but
  may be disabled to save space for embedded applications.
* `no-std`: Disables features that require the standard library and cannot
  be cheaply polyfilled. Specifically, this feature disables heap
  allocation, so `Debug`, `Display`, and `Serialize` become reliant on
  preallocated buffers.
