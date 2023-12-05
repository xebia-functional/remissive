//! Herein is the complete framework for Remissive, modulo the
//! `remissive_macros` crate, which is recommended for use with Remissive to
//! further streamline development and reduce boilerplate.

use core::mem::size_of;
#[cfg(doc)]
use core::num::Wrapping;
use core::sync::atomic::Ordering;

use portable_atomic::AtomicU32;
use postcard::from_bytes;
#[cfg(not(feature = "no-std"))]
use postcard::to_allocvec;
use postcard::to_vec;
use serde::{Deserialize, Serialize};
use serde::de::DeserializeOwned;

////////////////////////////////////////////////////////////////////////////////
//                            Message abstraction.                            //
////////////////////////////////////////////////////////////////////////////////

/// A message represents either a request, a response, or a notification.
/// Messages are transport neutral, and may be encoded for use over either UDP,
/// REST, or WebSocket. `Body` is the static type of the semantic
/// [body](Self::body) of the message.
#[derive(Serialize, Deserialize)]
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct Message<Body>
{
	/// The conversation identifier, which transiently uniquely identifies this
	/// message relative to the enclosing stream. Conversation identifiers are
	/// [strictly&#32;increasing]. It is permissible to reuse identifiers so
	/// long as no two active conversations bear the same identifier, so a
	/// generator may use a [wrapping](Wrapping) policy if care is taken.
	/// Conversations are short-lived, so the 32-bit representation space
	/// provides vastly more than enough leeway to ensure that this property
	/// holds across wraps. Conversations begin with requests, so conversation
	/// identifiers are allocated by the requester, which is usually, but not
	/// necessarily, the client.
	///
	/// [strictly&#32;increasing]: https://mathworld.wolfram.com/StrictlyIncreasingFunction.html
	pub id: u32,

	/// The message body, which carries the semantic payload of the message.
	/// This is generic in order provide static polymorphism, which supports
	/// reuse of the infrastructure among different transports or applications.
	/// This type would usually be an `enum` where each variant wraps a `struct`
	/// that fully encapsulates the complete state of the message.
	pub body: Body
}

/// Automatically implement [Clone] for [`Message<Body>`](Message) whenever
/// `Body` implements [Clone].
impl<Body: Clone> Clone for Message<Body>
{
	fn clone(&self) -> Self
	{
		Self { id: self.id, body: self.body.clone() }
	}
}

/// Automatically implement [Copy] for [`Message<Body>`](Message) whenever
/// `Body` implements [Clone] and [Copy].
impl<Body: Clone + Copy> Copy for Message<Body>
{
	// No body required.
}

/// Automatically implement [PartialEq] for [`Message<Body>`](Message) whenever
/// `Body` implements [PartialEq].
impl<Body: PartialEq> PartialEq for Message<Body>
{
	fn eq(&self, other: &Self) -> bool
	{
		self.id == other.id && self.body == other.body
	}
}

/// Automatically implement [Eq] for [`Message<Body>`](Message) whenever `Body`
/// implements [PartialEq] and [Eq].
impl<Body: PartialEq + Eq> Eq for Message<Body>
{
	// No body required.
}

#[cfg(feature = "display")]
impl<Body: core::fmt::Display> core::fmt::Display for Message<Body>
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result
	{
		let Self { id, body } = self;
		write!(f, "message\n\tid: {id}\n\tbody: {body}")
	}
}

impl<Body: Serialize + DeserializeOwned> Message<Body>
{
	/// Answer a conservative heuristic for the number of bytes required to
	/// serialize a [Message]. Given that the serialization format uses a
	/// variable-length encoding for certain primitive types, the goal is to
	/// ensure that this conservative estimate is greater than or equal to the
	/// actual number of bytes required to serialize the message _when all
	/// message parts are statically sized_. The heuristic will likely be
	/// _wrong_ for messages that contain variable-length objects, e.g., `Vec`,
	/// `String`, `HashMap`, etc. Use with caution!
	#[inline]
	pub const fn serial_buffer_size() -> usize
	{
		// Given that (1) the `size_of` operation includes alignment and (2) the
		// wire format only requires 19 bytes to encode u128::MAX, and that this
		// is the largest inflation among the primitive types, we can safely
		// multiply by two to account for maximum variability.
		size_of::<Self>() << 1
	}

	/// Serialize the receiver into a standard [vector](alloc::vec::Vec).
	///
	/// ### Errors
	/// Answer an [Error](super::Error) if serialization fails for any reason.
	#[cfg(not(feature = "no-std"))]
	#[inline]
	pub fn serialize_alloc(&self) -> Result<alloc::vec::Vec<u8>, super::Error>
	{
		to_allocvec(&self)
	}

	/// Serialize the receiver into a fixed-size stack-allocated
	/// [vector](heapless::Vec).
	///
	/// ### Errors
	/// Answer an [Error](super::Error) if serialization fails for any reason.
	#[inline]
	pub fn serialize<const N: usize>(
		&self
	) -> Result<heapless::Vec<u8, N>, super::Error>
	{
		to_vec(&self)
	}

	/// Deserialize an instance of [Message] from the specified byte array.
	///
	/// ### Errors
	/// Answer an [Error](postcard::Error) if deserialization fails for any
	/// reason.
	#[inline]
	pub fn deserialize(bytes: impl AsRef<[u8]>) -> Result<Self, super::Error>
	{
		from_bytes(bytes.as_ref())
	}
}

impl<Body> Message<Body>
{
	/// Construct a [`Message`] with the given complete state.
	#[inline]
	pub const fn with_id_and_body(id: u32, body: Body) -> Self
	{
		Self { id, body }
	}

	/// Construct a [`Message`] with the specified [body](Self::body). Allocate
	/// the next available identifier from the specified
	/// [atomic&#32;counter](AtomicU32), using [`SeqCst`](Ordering::SeqCst)
	/// [ordering](Ordering), thereby ensuring thread safety.
	pub fn with_body(generator: &AtomicU32, body: Body) -> Self
	{
		Self
		{
			id: generator.fetch_add(1, Ordering::SeqCst),
			body
		}
	}

	/// Construct a reply to the receiver by invoking the specified `builder`
	/// function. Use the receiver's identifier as the conversation identifier.
	pub fn reply(&self, builder: impl FnOnce() -> Body) -> Self
	{
		Self
		{
			id: self.id,
			body: builder()
		}
	}
}

////////////////////////////////////////////////////////////////////////////////
//                            Version negotiation.                            //
////////////////////////////////////////////////////////////////////////////////

/// A protocol version. The version `0` is reserved, and should not appear as a
/// valid protocol version within any protocol derived from this crate. This
/// permits it to act as a sensible default.
#[derive(
	Copy, Clone,
	Default,
	PartialEq, Eq,
	PartialOrd, Ord,
	Serialize, Deserialize
)]
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct ProtocolVersion(pub u32);

impl From<u32> for ProtocolVersion
{
	/// Allow convenient conversion from a `u32`.
	fn from(value: u32) -> Self
	{
		Self(value)
	}
}

impl From<ProtocolVersion> for u32
{
	/// Allow convenient conversion to a `u32`.
	fn from(value: ProtocolVersion) -> Self
	{
		value.0
	}
}

#[cfg(feature = "display")]
impl core::fmt::Display for ProtocolVersion
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result
	{
		write!(f, "version #{}", self.0)
	}
}

/// Client request to propose a protocol version for subsequent communication.
/// If the server supports the
/// [preferred&#32;version](ProposeVersion::preferred_version), then it must
/// transmit an [AcceptedVersion] message to complete version negotiation.
///
/// Reusable across protocols and message lexicons; just embed it within a
/// variant in the `enum` that concretizes the `Body` parameter of [Message].
/// Automatically inserted into an `enum` annotated with `#[remissive_target]`.
/// This attribute is available via the `remissive_macros` crate.
#[derive(Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct ProposeVersion
{
	/// The preferred version of the protocol.
	pub preferred_version: ProtocolVersion
}

impl From<ProtocolVersion> for ProposeVersion
{
	/// Allow convenient conversion from a [ProtocolVersion].
	fn from(preferred_version: ProtocolVersion) -> Self
	{
		Self { preferred_version }
	}
}

impl From<u32> for ProposeVersion
{
	/// Allow convenient conversion from a `u32`.
	fn from(preferred_version: u32) -> Self
	{
		Self { preferred_version: preferred_version.into() }
	}
}

#[cfg(feature = "display")]
impl core::fmt::Display for ProposeVersion
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result
	{
		write!(f, "ProposeVersion({})", self.preferred_version)
	}
}

impl ProposeVersion
{
	/// Negotiate a protocol version. If `supported` includes the
	/// [preferred&#32;version](ProposeVersion::preferred_version), then answer
	/// an [AcceptedVersion]. Otherwise, answer a [SupportedVersions] message
	/// that enumerates up to four (4) server-supported versions, among which
	/// the client may select for subsequent version negotiation.
	pub fn negotiate(
		&self,
		supported: impl AsRef<[ProtocolVersion]>
	) -> Result<AcceptedVersion, SupportedVersions>
	{
		let supported = supported.as_ref();
		if supported.contains(&self.preferred_version)
		{
			Ok(AcceptedVersion)
		}
		else
		{
			let ultima = max_lt(supported, None).copied();
			let penult = max_lt(supported, ultima).copied();
			let antepenult = max_lt(supported, penult.or(ultima)).copied();
			let preantepenult =
				max_lt(supported, antepenult.or(penult).or(ultima)).copied();
			Err(SupportedVersions {
				versions: [ultima, penult, antepenult, preantepenult]
			})
		}
	}
}

/// Server response to a [ProposeVersion], indicating that the proposed version
/// was accepted. Version negotiation is complete, and ordinary communication
/// may now proceed.
///
/// Reusable across protocols and message lexicons; just embed it within a
/// variant in the `enum` that concretizes the `Body` parameter of [Message].
/// Automatically inserted into an `enum` annotated with `#[remissive_target]`.
/// This attribute is available via the `remissive_macros` crate.
#[derive(Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct AcceptedVersion;

#[cfg(feature = "display")]
impl core::fmt::Display for AcceptedVersion
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result
	{
		write!(f, "AcceptedVersion")
	}
}

/// Server response to a [ProposeVersion], indicating that the proposed version
/// was rejected. The payload enumerates up to four (4) server-supported
/// versions, among which the client may select for subsequent version
/// negotiation. For connected transports, the server disconnects the client.
///
/// If the client supports any of the rebuttal versions, then the client sends a
/// subsequent [ProposeVersion] in a new conversation (and in a new connection
/// for connected transports) that includes the preferred rebuttal version. At
/// its discretion, and for an unspecified but limited time, a server that
/// receives consecutive [ProposeVersion] requests bearing unsupported versions
/// may blacklist the transgressing endpoint in order to reduce the impact of a
/// denial of service (DoS) attack.
///
/// Reusable across protocols and message lexicons; just embed it within a
/// variant in the `enum` that concretizes the `Body` parameter of [Message].
/// Automatically inserted into an `enum` annotated with `#[remissive_target]`.
/// This attribute is available via the `remissive_macros` crate.
#[derive(Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct SupportedVersions
{
	/// The versions supported by the server. Should generally be the newest
	/// four (4) protocol versions.
	pub versions: [Option<ProtocolVersion>; 4]
}

impl From<ProtocolVersion> for SupportedVersions
{
	/// Construct a singleton version list from a [ProtocolVersion].
	fn from(value: ProtocolVersion) -> Self
	{
		SupportedVersions { versions: [Some(value), None, None, None] }
	}
}

impl From<u32> for SupportedVersions
{
	/// Construct a singleton version list from a `u32`.
	fn from(value: u32) -> Self
	{
		SupportedVersions { versions: [Some(value.into()), None, None, None] }
	}
}

#[cfg(feature = "display")]
impl core::fmt::Display for SupportedVersions
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result
	{
		write!(f, "SupportedVersions(")?;
		let mut first = true;
		for version in self.versions.into_iter().flatten()
		{
			if !first
			{
				writeln!(f, ", ")?;
			}
			writeln!(f, "#{}", version.0)?;
			first = false;
		}
		write!(f, ")")
	}
}

////////////////////////////////////////////////////////////////////////////////
//                             Acknowledgements.                              //
////////////////////////////////////////////////////////////////////////////////

/// Stateless general purpose acknowledgement. Reusable across protocols and
/// message lexicons; just embed it within a variant in the `enum` that
/// concretizes the `Body` parameter of [Message].
///
/// Reusable across protocols and message lexicons; just embed it within a
/// variant in the `enum` that concretizes the `Body` parameter of [Message].
/// Automatically inserted into an `enum` annotated with `#[remissive_target]`.
/// This attribute is available via the `remissive_macros` crate.
#[derive(Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(feature = "debug", derive(Debug))]
pub struct Acknowledged;

#[cfg(feature = "display")]
impl core::fmt::Display for Acknowledged
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result
	{
		write!(f, "Acknowledged")
	}
}

////////////////////////////////////////////////////////////////////////////////
//                                 Utilities.                                 //
////////////////////////////////////////////////////////////////////////////////

/// Answer the maximum value of `slice` less than `cap`; but if `cap` is
/// `None`, just answer the maximum value of `slice`.
#[inline]
fn max_lt<T: Copy + Ord>(slice: &[T], cap: Option<T>) -> Option<&T>
{
	match cap
	{
		None => slice.iter().max(),
		Some(cap) => slice.iter().filter(|&value| *value < cap).max()
	}
}

////////////////////////////////////////////////////////////////////////////////
//                                   Tests.                                   //
////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
/// Herein are tests.
mod test
{
	use portable_atomic::AtomicU32;

	use crate::messages::{Message, ProposeVersion};

	/// Test the basics.
	#[test]
	#[allow(clippy::unit_cmp)]
	#[allow(clippy::clone_on_copy)]
	fn basics()
	{
		// We have to take care not to invoke debug formatting for any of our
		// types, because that would require the `debug` feature, which is not
		// guaranteed to be enabled for this test. So the code will look a bit
		// strange.
		let message = Message::with_id_and_body(0, ());
		assert_eq!(message.id, 0);
		assert_eq!(message.body, ());
		let message2 = Message::with_id_and_body(0, ());
		assert_eq!(message2.id, message.id);
		assert_eq!(message2.body, message.body);
		let message2 = message.clone();
		assert_eq!(message2.id, message.id);
		assert_eq!(message2.body, message.body);
	}

	/// Test construction with an atomic generator.
	#[test]
	fn generator()
	{
		let generator = AtomicU32::new(0);
		let message = Message::with_body(&generator, ());
		assert_eq!(message.id, 0);
		let message = Message::with_body(&generator, ());
		assert_eq!(message.id, 1);
		let message = Message::with_body(&generator, ());
		assert_eq!(message.id, 2);
	}

	/// Test the `PartialEq` implementation.
	#[cfg(feature = "debug")]
	#[test]
	#[allow(clippy::clone_on_copy)]
	fn partial_eq()
	{
		let message = Message::with_id_and_body(0, ());
		let message2 = Message::with_id_and_body(0, ());
		assert_eq!(message2, message);
		let message2 = message.clone();
		assert_eq!(message2, message);
	}

	/// Test the `Display` implementation.
	#[cfg(all(feature = "display", not(feature = "no-std")))]
	#[test]
	fn display()
	{
		use alloc::string::ToString;
		let message = Message::with_id_and_body(0, 42);
		assert_eq!(&message.to_string(), "message\n\tid: 0\n\tbody: 42");
	}

	/// Test the conservative serialization buffer size heuristic.
	#[test]
	fn serial_buffer_size()
	{
		assert_eq!(Message::<()>::serial_buffer_size(), 8);
		assert_eq!(Message::<bool>::serial_buffer_size(), 16);
		assert_eq!(Message::<char>::serial_buffer_size(), 16);
		assert_eq!(Message::<u8>::serial_buffer_size(), 16);
		assert_eq!(Message::<u16>::serial_buffer_size(), 16);
		assert_eq!(Message::<u32>::serial_buffer_size(), 16);
		assert_eq!(Message::<u64>::serial_buffer_size(), 32);
		assert_eq!(Message::<u128>::serial_buffer_size(), 64);
		assert_eq!(Message::<i8>::serial_buffer_size(), 16);
		assert_eq!(Message::<i16>::serial_buffer_size(), 16);
		assert_eq!(Message::<i32>::serial_buffer_size(), 16);
		assert_eq!(Message::<i64>::serial_buffer_size(), 32);
		assert_eq!(Message::<i128>::serial_buffer_size(), 64);
		assert_eq!(Message::<f32>::serial_buffer_size(), 16);
		assert_eq!(Message::<f64>::serial_buffer_size(), 32);
		assert_eq!(Message::<[u8; 0]>::serial_buffer_size(), 8);
		assert_eq!(Message::<[u8; 1]>::serial_buffer_size(), 16);
		assert_eq!(Message::<[u8; 2]>::serial_buffer_size(), 16);
		assert_eq!(Message::<[u8; 3]>::serial_buffer_size(), 16);
		assert_eq!(Message::<[u8; 4]>::serial_buffer_size(), 16);
		assert_eq!(Message::<[u8; 5]>::serial_buffer_size(), 24);
		assert_eq!(Message::<[u8; 6]>::serial_buffer_size(), 24);
		assert_eq!(Message::<[u8; 7]>::serial_buffer_size(), 24);
		assert_eq!(Message::<[u8; 8]>::serial_buffer_size(), 24);
		assert_eq!(Message::<[u8; 9]>::serial_buffer_size(), 32);
	}

	/// Test serialization and deserialization.
	#[cfg(not(feature = "no-std"))]
	#[test]
	fn serialization_alloc()
	{
		// We have to take care not to invoke debug formatting for any of our
		// types, because that would require the `debug` feature, which is not
		// guaranteed to be enabled for this test. So the code will look a bit
		// strange.
		let message = Message::with_id_and_body(0, 42);
		let bytes = message.serialize_alloc().unwrap();
		let message2 = Message::deserialize(bytes).unwrap();
		assert_eq!(message2, message);
	}

	/// Test serialization and deserialization.
	#[test]
	fn serialization()
	{
		const N: usize = Message::<i32>::serial_buffer_size();
		let message = Message::with_id_and_body(0, 42);
		let bytes = message.serialize::<N>().unwrap();
		let expected = heapless::Vec::<u8, N>::from_slice(&[0, 84]).unwrap();
		assert_eq!(bytes, expected);
		let message2 = Message::<i32>::deserialize(&bytes).unwrap();
		assert_eq!(message2.id, message.id);
		assert_eq!(message2.body, message.body);
	}

	/// Test version negotiation.
	#[test]
	fn version_negotiation()
	{
		// We have to take care not to invoke debug formatting for any of our
		// types, because that would require the `debug` feature, which is not
		// guaranteed to be enabled for this test. So the code will look a bit
		// strange.
		let supported = [2.into(), 5.into(), 3.into(), 1.into(), 4.into()];
		let proposal = ProposeVersion::from(3);
		let accepted = proposal.negotiate(supported);
		assert!(accepted.is_ok());
		let proposal = ProposeVersion::from(6);
		let rejected = proposal.negotiate(supported);
		match rejected
		{
			Ok(_) => unreachable!("should have been rejected"),
			Err(rejected) =>
			{
				assert_eq!(rejected.versions.len(), 4);
				assert_eq!(rejected.versions[0].unwrap().0, 5);
				assert_eq!(rejected.versions[1].unwrap().0, 4);
				assert_eq!(rejected.versions[2].unwrap().0, 3);
				assert_eq!(rejected.versions[3].unwrap().0, 2);
			}
		}
	}

	/// Test that replying continues the conversation.
	#[test]
	fn reply()
	{
		struct SumRequest { _a: u32, _b: u32 }
		struct Sum { result: u32 }
		enum Body { SumRequest(SumRequest), Sum(Sum) }
		let request = Message::with_id_and_body(
			0,
			Body::SumRequest(SumRequest { _a: 1, _b: 2 })
		);
		let response = request.reply(|| Body::Sum(Sum { result: 3 }));
		assert_eq!(response.id, request.id);
		assert!(matches!(response.body, Body::Sum(Sum { result: 3 })));
	}
}
