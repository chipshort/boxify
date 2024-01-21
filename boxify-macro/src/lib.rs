//! Proc-macro crate for `boxify` crate.
//! Please see [`::boxify`] for more information.
use std::str::FromStr;

use litrs::{BoolLit, Literal};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parse_quote,
    visit_mut::{self, VisitMut},
    Expr,
};

extern crate proc_macro;

/// Places the given value on the heap, like [`Box::new`], but without creating it on the stack first.
/// This is useful for values that are too big to be created on the stack.
///
/// # Examples
///
/// ```rust,ignore
/// use boxify::boxify;
///
/// let b = boxify!([42u32; 1024 * 1024 * 1024]);
/// assert_eq!(b[0], 42);
/// ```
#[proc_macro]
pub fn boxify(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let value_to_box = syn::parse_macro_input!(item as Expr);

    boxify_impl(value_to_box).into()
}

fn boxify_impl(value_to_box: Expr) -> TokenStream {
    if let Some(zero_alloc) = zero_alloc_special_handling(&value_to_box) {
        return zero_alloc;
    }

    let validate_fields = validate_fields(value_to_box.clone());

    let final_value_ptr = parse_quote! {
        __boxify_final_value_ptr
    };
    let instantiation_code = match value_to_box {
        // listing them here explicitly in order to throw an error for any other type
        // since only these here are allocated directly on the heap right now
        Expr::Struct(_) | Expr::Repeat(_) | Expr::Tuple(_) | Expr::Call(_) => {
            fill_ptr(&final_value_ptr, &value_to_box)
        }
        _ => todo!("Implement for more types"),
    };

    quote! {{
        let mut __boxify_final_value = ::boxify::new_box_uninit_typed(#validate_fields);
        let __boxify_final_value_ptr = __boxify_final_value.as_mut_ptr();

        #instantiation_code

        // SAFETY: We just filled the memory with a valid value
        unsafe { ::boxify::assume_init(__boxify_final_value) }
    }}
}

/// Special handling for `[0; N]` arrays, which can be allocated with `new_box_zeroed`.
fn zero_alloc_special_handling(value_to_box: &Expr) -> Option<TokenStream> {
    if let Expr::Repeat(array) = value_to_box {
        let value_expr = &*array.expr;
        // parse the literal to check if it's all zero bytes
        if let Ok(literal) = Literal::parse(value_expr.to_token_stream().to_string()) {
            let is_zero = match &literal {
                Literal::Integer(i) if i.value::<u128>() == Some(0) => true,
                Literal::Bool(BoolLit::False) => true,
                Literal::Float(f) if f64::from_str(f.number_part()) == Ok(0f64) => true,
                Literal::Char(c) if c.value() == '\0' => true,
                Literal::Byte(b) if b.value() == 0 => true,
                _ => false,
            };

            // if the array is all zero, we can just allocate a zeroed memory chunk
            if is_zero {
                return Some(quote! {
                    // SAFETY: We checked above that the array value should be all zero bytes
                    unsafe {
                        // using the `_typed` version here for proper type inference
                        ::boxify::new_box_zeroed_typed(::boxify::TypeInferer::new(|| {
                            #array
                        }))
                    }
                });
            }
        }
    }
    None
}

/// Generates code that validates that all fields of a struct were provided.
fn validate_fields(mut expr: Expr) -> proc_macro2::TokenStream {
    /// Outputs code that creates a value of the same type as its input
    /// without taking ownership of the input.
    struct CloneType;

    impl VisitMut for CloneType {
        fn visit_field_value_mut(&mut self, v: &mut syn::FieldValue) {
            let expr = &v.expr;
            // Replace the expression with a clone of the expression.
            v.expr = parse_quote! {
                // SAFETY: we never execute this code,
                // we just use it for type checking / inference
                unsafe { ::boxify::clone(&#expr) }
            };
            visit_mut::visit_field_value_mut(self, v);
        }
    }

    CloneType.visit_expr_mut(&mut expr);

    // Wrap this in a `TypeInferer` to prevent misuse
    quote! {
        ::boxify::TypeInferer::new(||
        {
            #expr
        })
    }
}

/// Fills a pointer with a value by matching on the value and choosing the
/// appropriate method to fill the pointer.
/// This is needed to be able to introduce special-handling for arrays and
/// potentially big structs.
fn fill_ptr(ptr: &Expr, value: &Expr) -> proc_macro2::TokenStream {
    match value {
        Expr::Array(_array) => {
            todo!("array literals are currently not supported");
        }
        Expr::Repeat(array) => fill_array(ptr, array),
        Expr::Struct(strct) => fill_struct_fields(ptr, strct),
        Expr::Tuple(tuple) => fill_tuple(ptr, &tuple.elems),
        Expr::Call(call) => {
            if let Expr::Path(_) = &*call.func {
                // TODO: we assume that we are given a struct for now
                fill_tuple(ptr, &call.args)
            } else {
                unimplemented!("function calls are not supported")
            }
        }
        e => {
            // fallback to creating the value on the stack and writing it to
            // the pointer from there
            quote! {
                unsafe { #ptr.write(#e); }
            }
        }
    }
}

/// Fills a struct by filling all its fields.
fn fill_struct_fields(strct_ptr: &Expr, strct: &syn::ExprStruct) -> proc_macro2::TokenStream {
    let instantiation_codes = strct.fields.iter().map(|field| {
        let ident = &field.member;
        let expr = &field.expr;

        let field_ptr = parse_quote! {
            core::ptr::addr_of_mut!((*#strct_ptr).#ident)
        };
        fill_ptr(&field_ptr, expr)
    });
    quote! {
        #(#instantiation_codes);*
    }
}

fn fill_array(ptr: &Expr, array: &syn::ExprRepeat) -> proc_macro2::TokenStream {
    let value = &*array.expr;
    quote! {
        // SAFETY: We only call this on uninitialized memory
        unsafe { ::boxify::fill_array(#ptr, #value); }
    }
}

/// Fills a tuple by filling all its elements.
fn fill_tuple(
    ptr: &Expr,
    elems: &syn::punctuated::Punctuated<Expr, syn::token::Comma>,
) -> proc_macro2::TokenStream {
    let instantiation_codes = elems.iter().enumerate().map(|(index, value)| {
        let index = syn::Index::from(index);
        let field_ptr = parse_quote! {
            core::ptr::addr_of_mut!((*#ptr).#index)
        };
        fill_ptr(&field_ptr, &value)
    });
    quote! {
        #(#instantiation_codes);*
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_fields() {
        let expr = parse_quote! {
            Parent {
                child: Child {
                    value: 42,
                    grand_child: GrandChild {
                        vec: v,
                        huge_array: [42; 1024 * 1024 * 1024],
                    },
                },
            }
        };
        let tokens = validate_fields(expr);

        let expected = quote! {
            ::boxify::TypeInferer::new(|| {
                Parent {
                    child: unsafe { ::boxify::clone(&Child {
                        value: unsafe { ::boxify::clone(&42) },
                        grand_child: unsafe { ::boxify::clone(&GrandChild {
                            vec: unsafe { ::boxify::clone(&v) },
                            huge_array: unsafe { ::boxify::clone(&[42; 1024 * 1024 * 1024]) },
                        }) },
                    }) },
                }
            })
        };
        assert_eq!(tokens.to_string(), expected.to_string());
    }
}
