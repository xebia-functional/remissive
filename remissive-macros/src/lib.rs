//! This crate provides the `#[remissive]` and `#[remissive_target]` macros for
//! use with the `remissive` crate. These macros allow boilerplate-free creation
//! of a lexicon of protocol-specific message types, allowing the user to focus
//! creative energy on payloads rather than common ceremony (e.g., version
//! negotiation) and message framing.
//!
//! ### Examples
//!
//! Here's an example of a protocol that inherits version negotiation and
//! acknowledgment from `remissive` and then defines three additional message
//! types of its own:
//!
//! ```rust
//! # use remissive::*;
//! # use remissive_macros::{remissive, remissive_target};
//! # use serde::{Serialize, Deserialize};
//! #[remissive(Body, 0)]
//! #[derive(Debug, PartialEq)]
//! struct A;
//!
//! #[remissive(Body, 1)]
//! #[derive(Debug, PartialEq)]
//! struct B(u32);
//!
//! #[remissive(Body, 2)]
//! #[derive(Debug, PartialEq)]
//! struct C
//! {
//!     a: u64,
//!     b: f64
//! }
//!
//! #[remissive_target]
//! #[derive(Debug, PartialEq)]
//! enum Body
//! {
//!     // Field definitions are filled in by the `remissive_target` macro. The
//!     // generated variants, in definition order, are:
//!     // * `ProposeVersion`
//!     // * `AcceptedVersion`
//!     // * `SupportedVersions`
//!     // * `Acknowledged`
//!     // * `A`
//!     // * `B`
//!     // * `C`
//! }
//!
//! let propose_version = Body::ProposeVersion(3.into());
//! let accepted_version = Body::AcceptedVersion(AcceptedVersion);
//! let supported_versions = Body::SupportedVersions(SupportedVersions {
//!     versions: [Some(2.into()), Some(1.into()), None, None]
//! });
//! let acknowledged = Body::Acknowledged(Acknowledged);
//! let a = Body::A(A);
//! let b = Body::B(B(42));
//! let c = Body::C(C { a: 42, b: 3.14 });
//!
//! let message: Message<Body> = Message::with_id_and_body(0, propose_version);
//! const N: usize = Message::<Body>::serial_buffer_size();
//! let serialized = message.serialize::<N>().unwrap();
//! let deserialized = Message::<Body>::deserialize(&serialized).unwrap();
//! assert_eq!(message, deserialized);
//! ```
//!
//! Here's the example from the `Elementary Usage` section of the `remissive`
//! crate documentation, rewritten to use the `#[remissive]` and
//! `#[remissive_target]` macros:
//!
//! ```rust
//! # use remissive::{HeaplessVec, Message};
//! # use remissive_macros::{remissive, remissive_target};
//! # use serde::{Serialize, Deserialize};
//! #[remissive(Body, 0)]
//! #[derive(PartialEq, Debug)]
//! struct ComputeRequest { a: u32, b: u32 }
//!
//! #[remissive(Body, 1)]
//! #[derive(PartialEq, Debug)]
//! struct ComputeResponse { result: u32 }
//!
//! #[remissive_target]
//! #[derive(PartialEq, Debug)]
//! enum Body {
//!     // Field definitions are filled in by the `remissive_target` macro. The
//!     // generated variants, in definition order, are:
//!     // * `ProposeVersion`
//!     // * `AcceptedVersion`
//!     // * `SupportedVersions`
//!     // * `Acknowledged`
//!     // * `ComputeRequest`
//!     // * `ComputeResponse`
//! }
//!
//! type Msg = Message<Body>;
//! const N: usize = Msg::serial_buffer_size();
//!
//! // Hypothetical message to request a computation.
//! let message = Msg::with_id_and_body(
//!     1, Body::ComputeRequest(ComputeRequest { a: 1, b: 2 }));
//! let serialized: HeaplessVec<N> = message.serialize().unwrap();
//! let deserialized = Msg::deserialize(&serialized).unwrap();
//! assert_eq!(message, deserialized);
//!
//! // Hypothetical message to respond to a computation request.
//! let message = Msg::with_id_and_body(
//!    1, Body::ComputeResponse(ComputeResponse { result: 3 }));
//! let serialized: HeaplessVec<N> = message.serialize().unwrap();
//! let deserialized = Msg::deserialize(&serialized).unwrap();
//! assert_eq!(message, deserialized);
//! ```

extern crate self as remissive_macros;

use std::cmp::Ordering;
use proc_macro2::{Ident, Span, TokenStream};
use std::collections::{BTreeSet, HashMap};
use std::collections::hash_map::Entry;
use std::ops::Not;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;

use once_cell::sync::Lazy;
use quote::{quote, ToTokens};
use syn::{Data, DeriveInput, LitInt, parenthesized, parse_macro_input, Token};
use syn::parse::{Parse, ParseStream};

////////////////////////////////////////////////////////////////////////////////
//                              Message tagging.                              //
////////////////////////////////////////////////////////////////////////////////

/// Mark the annotated type as a message for unification within the specified
/// `enum`. The target `enum` must be annotated with `#[remissive_target]`.
/// Automatically derives `serde::Serialize` and `serde::Deserialize` for the
/// annotated type.
///
/// The first argument is the unqualified identifier of the unification `enum`.
/// Every type annotated with `#[remissive(X, _)]` will be unified with every
/// other such type within the same crate into a single enum `X` with all of the
/// variants of the constituent types.
///
/// The second argument is the desired relative position of the variant within
/// the `enum`, giving the user some control over the wire format. The first
/// user type should claim position `0`. All user types will follow every system
/// type, and gaps in the final numbering will be filled in with reserved
/// variants, e.g., `RESERVED_15`, for future proofing.
///
/// Any remaining arguments correspond to directives, which may be specified in
/// arbitrary order. The following directives are supported:
///
/// * `manual_serde`: The user will implement `serde::Serialize` and
///   `serde::Deserialize` for the annotated type. The user may implement these
///   traits manually or use the `#[derive]` attribute.
/// * `name(<ident>)`: The name of the variant in the unification `enum`. If
///   omitted, the name of the variant is the same as the name of the annotated
///   type.
///
/// Does not rewrite the annotated data type, so other rewriting attributes may
/// be applied to it, and `#[derive]` attributes may be placed before or after
/// this attribute.
///
/// ### Examples
///
/// Here's an illustration of the `manual_serde` directive:
///
/// ```rust
/// # use std::fmt::{Formatter, Write};
/// # use remissive::*;
/// # use remissive_macros::{remissive, remissive_target};
/// # use serde::{Deserialize, Deserializer, Serialize, Serializer};
/// # use serde::de::{Error, Visitor};
/// #[remissive(Body, 0, manual_serde)]
/// #[derive(Serialize, Deserialize)]
/// struct A;
///
/// #[remissive(Body, 1, manual_serde)]
/// struct B;
///
/// impl Serialize for B {
///     fn serialize<S>(
///         &self,
///         serializer: S
///     ) -> Result<S::Ok, S::Error> where S: Serializer {
///         serializer.serialize_unit()
///     }
/// }
///
/// struct BDeserializer;
///
/// impl<'de> Visitor<'de> for BDeserializer {
///     type Value = B;
///
///     fn expecting(&self, formatter: &mut Formatter) -> std::fmt::Result {
///         formatter.write_str("unit")
///     }
///
///     fn visit_unit<E>(self) -> Result<Self::Value, E> where E: Error {
///         Ok(B)
///     }
/// }
///
/// impl<'de> Deserialize<'de> for B {
///     fn deserialize<D>(
///         deserializer: D
///     ) -> Result<Self, D::Error> where D: Deserializer<'de>
///     {
///         deserializer.deserialize_unit(BDeserializer)
///     }
/// }
///
/// #[remissive_target]
/// enum Body
/// {
///     // Field definitions are filled in by the `remissive_target` macro. The
///     // generated variants, in definition order, are:
///     // * `ProposeVersion`
///     // * `AcceptedVersion`
///     // * `SupportedVersions`
///     // * `Acknowledged`
///     // * `A`
/// }
/// ```
///
/// Here's an illustration of the `name` directive:
///
/// ```rust
/// # use remissive::*;
/// # use remissive_macros::{remissive, remissive_target};
/// # use serde::{Serialize, Deserialize};
/// #[remissive(Body, 0, name(Q))]
/// struct A;
///
/// #[remissive_target]
/// enum Body
/// {
///     // Field definitions are filled in by the `remissive_target` macro. The
///     // generated variants, in definition order, are:
///     // * `ProposeVersion`
///     // * `AcceptedVersion`
///     // * `SupportedVersions`
///     // * `Acknowledged`
///     // * `Q`
/// }
///
/// let q = Body::Q(A);
/// ```
#[proc_macro_attribute]
pub fn remissive(
	attr: proc_macro::TokenStream,
	item: proc_macro::TokenStream
) -> proc_macro::TokenStream
{
	catch_error(|| {
		let RemissiveAttribute {
			enum_ident,
			position,
			variant_name,
			manual_serde
		} = parse_macro_input!(attr as RemissiveAttribute);
		let mut registry = REGISTRY.lock().unwrap();
		let messages = match registry.entry(enum_ident.to_string())
		{
			Entry::Occupied(entry) => entry.into_mut(),
			Entry::Vacant(entry) => entry.insert(BTreeSet::new())
		};
		let source = item.clone();
		let source_name =
			parse_macro_input!(source as DeriveInput).ident.to_string();
		assert!(
			messages.iter().any(|r| r.source_name == source_name).not(),
			"message type `{}` already registered with unification enum `{}`",
			source_name,
			enum_ident
		);
		assert!(
			messages.iter().any(|r| r.position == position).not(),
			"position `{}` already claimed within unification enum `{}`",
			position,
			enum_ident
		);
		let variant_name = variant_name
			.map(|v| v.to_string())
			.unwrap_or_else(|| source_name.clone());
		assert!(
			messages.iter().any(|r| r.variant_name == variant_name).not(),
			"variant name `{}` already claimed within unification enum `{}`",
			variant_name,
			enum_ident
		);
		messages.insert(Registration {
			source_name,
			position,
			variant_name
		});
		let derive = match manual_serde
		{
			true => quote! { },
			false => quote! { #[derive(serde::Serialize, serde::Deserialize)] }
		};
		let item: TokenStream = item.into();
		let out = quote! {
			#derive
			#item
		};
		out.into()
	})
}

/// Mark the annotated _empty_ `enum` as the unification target for a complete
/// lexicon of message types. Automatically derives `serde::Serialize` and
/// `serde::Deserialize` for the annotated type. Every type annotated with
/// `#[remissive(X, _)]` will be unified into this `enum`. The variant names
/// correspond to the names of the constituent types.
///
/// Any arguments correspond to directives. The following directives are
/// supported:
///
/// * `no_version_negotiation`: Do not include the built-in version negotiation
///   variants in the unification target.
/// * `no_acknowledgment`: Do not include the built-in acknowledgment variant
///   in the unification target.
///
/// Unless `no_version_negotiation` is specified, the initial variants are:
///
/// * `ProposeVersion`
/// * `AcceptedVersion`
/// * `SupportedVersions`
/// * `Acknowledged`
///
/// Unless `no_acknowledgment` is specified, the next variant is:
///
/// * `Acknowledged`
///
/// All user message types occur after these variants, in the order specified by
/// the relative position ordinals supplied to `#[remissive]`.
///
/// To ensure that the constituent types are encountered and registered before
/// the unification target, the unification target must be defined after all of
/// the constituent types; this is safely accomplished by either (1) placing all
/// constituent types in the same module and then placing the unification target
/// after all constituents; or (2) placing the unification target in a module
/// that encloses all modules that define constituent types.
///
/// Expects to be able to rewrite the annotated `enum` _in situ_, so no other
/// rewriting attributes should be applied to it, and all `#[derive]` attributes
/// should be placed _after_ this attribute so that they see the complete set of
/// variants.
///
/// ### Examples
///
/// Here's an illustration of the `no_version_negotiation` directive:
///
/// ```rust
/// # use remissive::*;
/// # use remissive_macros::{remissive, remissive_target};
/// # use serde::{Serialize, Deserialize};
/// #[remissive(Body, 0)]
/// struct A;
///
/// #[remissive_target(no_version_negotiation)]
/// enum Body
/// {
///     // Field definitions are filled in by the `remissive_target` macro. The
///     // generated variants, in definition order, are:
///     // * `Acknowledged`
///     // * `A`
/// }
/// ```
///
/// Here's an illustration of the `no_acknowledgment` directive:
///
/// ```rust
/// # use remissive::*;
/// # use remissive_macros::{remissive, remissive_target};
/// # use serde::{Serialize, Deserialize};
/// #[remissive(Body, 0)]
/// struct A;
///
/// #[remissive_target(no_version_negotiation)]
/// enum Body
/// {
///     // Field definitions are filled in by the `remissive_target` macro. The
///     // generated variants, in definition order, are:
///     // * `ProposeVersion`
///     // * `AcceptedVersion`
///     // * `SupportedVersions`
///     // * `A`
/// }
/// ```
///
/// Here's an illustration of an absolutely bare-bones protocol that does not
/// inherit any built-in variants:
///
/// ```rust
/// # use remissive::*;
/// # use remissive_macros::{remissive, remissive_target};
/// # use serde::{Serialize, Deserialize};
/// #[remissive(Body, 0)]
/// struct A;
///
/// #[remissive_target(no_version_negotiation, no_acknowledgment)]
/// enum Body
/// {
///     // Field definitions are filled in by the `remissive_target` macro. The
///     // generated variants, in definition order, are:
///     // * `A`
/// }
/// ```
#[proc_macro_attribute]
pub fn remissive_target(
	attr: proc_macro::TokenStream,
	item: proc_macro::TokenStream
) -> proc_macro::TokenStream
{
	catch_error(|| {
		let RemissiveTargetAttribute {
			no_version_negotiation,
			no_acknowledgment
		} = parse_macro_input!(attr as RemissiveTargetAttribute);
		let item = parse_macro_input!(item as DeriveInput);
		// Take special care to preserve the visibility of the annotated item.
		let visibility = item.vis.to_token_stream();
		// Take special care to pass through any subsequent attributes.
		let attrs = item.attrs.iter().fold(TokenStream::new(), |mut acc, attr| {
			acc.extend(attr.to_token_stream());
			acc
		});
		assert!(matches!(item.data, Data::Enum(_)), "expected enum");
		let enum_ident = item.ident;
		let enum_name = enum_ident.to_string();
		let mut registry = REGISTRY.lock().unwrap();
		let mut messages = registry
			.remove(&enum_name)
			.expect(
				"one or more data types annotated with `#[remissive]` to be \
				encountered before `#[remissive_target]`"
			)
			.into_iter()
			.map(|r| (r.position, (r.variant_name, r.source_name)))
			.collect::<HashMap<usize, (String, String)>>();
		messages.get(&0).expect("some message type must claim position `0`");
		let last_ordinal = messages.iter().map(|r| *r.0).max().unwrap();
		let body = (0..=last_ordinal)
			.map(|ordinal|
				messages.remove(&ordinal)
					.map(|(variant_name, source_name)| {
						let variant_name =
							Ident::new(&variant_name, Span::call_site());
						let source_name =
							Ident::new(&source_name, Span::call_site());
						quote! { #variant_name(#source_name), }
					})
					.unwrap_or_else(|| {
						let id = format!("RESERVED_{}", ordinal);
						let id = Ident::new(&id, Span::call_site());
						quote! { #id, }
					})
			)
			.fold(TokenStream::new(), |mut acc, variant| {
				acc.extend(variant);
				acc
			});
		let mut builtins = TokenStream::new();
		if !no_version_negotiation
		{
			builtins.extend(quote! {
				ProposeVersion(remissive::ProposeVersion),
				AcceptedVersion(remissive::AcceptedVersion),
				SupportedVersions(remissive::SupportedVersions),
			});
		}
		if !no_acknowledgment
		{
			builtins.extend(quote! {
				Acknowledged(remissive::Acknowledged),
			});
		}
		let out = quote! {
			#attrs
			#[derive(serde::Serialize, serde::Deserialize)]
			#visibility enum #enum_ident
			{
				#builtins
				#body
			}
		};
		out.into()
	})
}

////////////////////////////////////////////////////////////////////////////////
//                              Parsing support.                              //
////////////////////////////////////////////////////////////////////////////////

/// Supporting type for parsing `#[remissive]` attributes.
struct RemissiveAttribute
{
	/// The unqualified identifier of the unification `enum`.
	enum_ident: Ident,

	/// The desired relative position of the variant within the `enum`.
	position: usize,

	/// The name of the variant in the unification `enum`, if it should differ
	/// from the name of the annotated type.
	variant_name: Option<Ident>,

	/// The optional `manual_serde` token after the relative position ordinal.
	manual_serde: bool
}

/// Supporting type for parsing `#[remissive]` attribute directives.
enum RemissiveDirective
{
	/// The `manual_serde` directive.
	ManualSerde,

	/// The `name` directive.
	Name(Ident)
}

impl RemissiveDirective
{
	/// Extract the name of the variant, if the receiver is
	/// [`Name`](Self::Name).
	fn name(self) -> Option<Ident>
	{
		match self
		{
			RemissiveDirective::ManualSerde => None,
			RemissiveDirective::Name(name) => Some(name)
		}
	}
}

impl Parse for RemissiveAttribute
{
	fn parse(input: ParseStream) -> syn::Result<Self>
	{
		let enum_ident = input.parse()?;
		input.parse::<Token![,]>()?;
		let position = input.parse::<LitInt>()?.base10_parse::<usize>().expect(
			"expected unsigned integer literal for position"
		);
		input.parse::<Option<Token![,]>>()?;
		let directives =
			input.parse_terminated(parse_remissive_directive, Token![,])?;
		let manual_serde = directives.iter()
			.any(|d| matches!(d, RemissiveDirective::ManualSerde));
		let variant_name = directives.into_iter()
			.find(|d| matches!(d, RemissiveDirective::Name(_)))
			.and_then(|name| name.name())
			.or(None);
		Ok(RemissiveAttribute {
			enum_ident,
			position,
			variant_name,
			manual_serde
		})
	}
}

/// Parse a single `#[remissive]` attribute directive.
fn parse_remissive_directive(
	input: ParseStream
) -> syn::Result<RemissiveDirective>
{
	let directive = input.parse::<Ident>()?;
	match directive
	{
		id if id == MANUAL_SERDE => Ok(RemissiveDirective::ManualSerde),
		id if id == VARIANT_NAME =>
		{
			let variant_name;
			parenthesized!(variant_name in input);
			let variant_name = variant_name.parse::<Ident>()?;
			Ok(RemissiveDirective::Name(variant_name))
		},
		id => panic!(
			"unrecognized directive `{}`; supported directives are: {}",
			id,
			REMISSIVE_DIRECTIVES
				.iter()
				.map(|s| format!("`{}`", s))
				.collect::<Vec<_>>()
				.join(", ")
		)
	}
}

/// The `manual_serde` directive for the `remissive` macro.
const MANUAL_SERDE: &str = "manual_serde";

/// The `name` directive for the `remissive` macro.
const VARIANT_NAME: &str = "name";

/// The set of all supported directives for the `remissive` macro.
const REMISSIVE_DIRECTIVES: &[&str] = &[MANUAL_SERDE, VARIANT_NAME];

/// Supporting type for parsing `#[remissive_target]` attributes.
struct RemissiveTargetAttribute
{
	/// Whether the `no_version_negotiation` directive was present.
	no_version_negotiation: bool,

	/// Whether the `no_acknowledgment` directive was present.
	no_acknowledgment: bool
}

impl Parse for RemissiveTargetAttribute
{
	fn parse(input: ParseStream) -> syn::Result<Self>
	{
		let directives = input.parse_terminated(Ident::parse, Token![,])?;
		directives.iter().all(|id| {
			if REMISSIVE_TARGET_DIRECTIVES.contains(&id.to_string().as_str())
			{
				true
			}
			else
			{
				panic!(
					"unrecognized directive `{}`; supported directives are: {}",
					id,
					REMISSIVE_TARGET_DIRECTIVES
						.iter()
						.map(|s| format!("`{}`", s))
						.collect::<Vec<_>>()
						.join(", ")
				)
			}
		});
		let no_version_negotiation =
			directives.iter().any(|id| id == NO_VERSION_NEGOTIATION);
		let no_acknowledgment =
			directives.iter().any(|id| id == NO_ACKNOWLEDGMENT);
		Ok(RemissiveTargetAttribute {
			no_version_negotiation,
			no_acknowledgment
		})
	}
}

/// The `no_version_negotiation` directive for the `remissive_target` macro.
const NO_VERSION_NEGOTIATION: &str = "no_version_negotiation";

/// The `no_acknowledgment` directive for the `remissive_target` macro.
const NO_ACKNOWLEDGMENT: &str = "no_acknowledgment";

/// The set of all supported directives for the `remissive_target` macro.
const REMISSIVE_TARGET_DIRECTIVES: &[&str] =
	&[NO_VERSION_NEGOTIATION, NO_ACKNOWLEDGMENT];

////////////////////////////////////////////////////////////////////////////////
//                              Error reporting.                              //
////////////////////////////////////////////////////////////////////////////////

/// For convenience, the macros just panic whenever they don't like something.
/// This function catches the panic and turns it into a compile error.
fn catch_error(
	f: impl FnOnce() -> proc_macro::TokenStream
) -> proc_macro::TokenStream
{
	match catch_unwind(AssertUnwindSafe(f))
	{
		Ok(tokens) => tokens,
		Err(message) =>
		{
			let message = match message.downcast_ref::<&'static str>()
			{
				Some(msg) => *msg,
				None =>
					match message.downcast_ref::<String>()
					{
						Some(msg) => msg.as_str(),
						None => "[unable to extract panic message]"
					}
			};
			quote! { compile_error!(#message); }.into()
		}
	}
}

////////////////////////////////////////////////////////////////////////////////
//                               Registration.                                //
////////////////////////////////////////////////////////////////////////////////

/// A registration of a message type with a unification `enum`.
#[derive(Hash, PartialEq, Eq)]
struct Registration
{
	/// The name of the message type.
	source_name: String,

	/// The relative position of the message type within the unification `enum`.
	position: usize,

	/// The name of the variant in the unification `enum`.
	variant_name: String
}

impl PartialOrd for Registration
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering>
	{
		Some(self.cmp(other))
	}
}

impl Ord for Registration
{
	fn cmp(&self, other: &Self) -> Ordering
	{
		self.position.cmp(&other.position)
	}
}

/// The shared registry of messages, organized by unifying `enum` name.
static REGISTRY: Lazy<Mutex<HashMap<String, BTreeSet<Registration>>>> =
	Lazy::new(|| Mutex::new(HashMap::new()));
