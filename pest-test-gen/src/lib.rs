use proc_macro::TokenStream;
//use proc_macro2::{Punct, Span, TokenStream as TokenStream2};
use proc_macro2::Span;
use proc_macro_error::{abort, abort_call_site, proc_macro_error};
use quote::{format_ident, quote, ToTokens};
use std::{borrow::Cow, path::PathBuf};
use syn::{
    parse_macro_input, AttributeArgs, Ident, Item, ItemMod, Lit, Meta, MetaList, MetaNameValue,
    NestedMeta, Path, PathArguments, PathSegment,
};
// use syn::{
//     parse_macro_input,
//     punctuated::Punctuated,
//     token::{Bang, Brace, Colon2, Comma, Dot, Eq, Fn, Gt, Let, Lt, Paren, RArrow, Semi},
//     AngleBracketedGenericArguments, AttributeArgs, Block, Expr, ExprLet, ExprLit, ExprMethodCall,
//     ExprPath, GenericArgument, Generics, Ident, Item, ItemFn, ItemMacro, ItemMod, Lit, LitStr,
//     Macro, MacroDelimiter, Meta, MetaNameValue, NestedMeta, Pat, PatIdent, Path, PathArguments,
//     PathSegment, ReturnType, Signature, Stmt, Type, TypePath, TypeTuple, Visibility,
// };
use walkdir::WalkDir;

struct Args {
    parser_path: Path,
    rule_path: Path,
    rule_ident: Ident,
    skip_rules: Vec<Ident>,
    dir: PathBuf,
    subdir: Option<PathBuf>,
    ext: String,
    recursive: bool,
    strict: bool,
    no_eoi: bool,
    lazy_static: bool,
}

impl Args {
    fn from(attr_args: Vec<NestedMeta>) -> Self {
        let mut attr_args_iter = attr_args.into_iter();

        // process required attrs
        let parser_path = match attr_args_iter.next() {
            Some(NestedMeta::Meta(Meta::Path(path))) => path,
            Some(other) => abort!(other, "Invalid parser type"),
            None => abort_call_site!("Missing required argument <parser>"),
        };
        let rule_path = match attr_args_iter.next() {
            Some(NestedMeta::Meta(Meta::Path(path))) => path,
            Some(other) => abort!(other, "Invalid rule"),
            None => abort_call_site!("Missing required argument <rule>"),
        };
        let rule_ident = match attr_args_iter.next() {
            Some(NestedMeta::Lit(Lit::Str(s))) => Ident::new(s.value().as_ref(), Span::call_site()),
            Some(other) => abort!(other, "Invalid rule name"),
            None => abort_call_site!("Missing required argument <root rule name>"),
        };

        let mut args = Args {
            parser_path,
            rule_path,
            rule_ident,
            skip_rules: Vec::new(),
            dir: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests")
                .join("pest"),
            subdir: None,
            ext: String::from("txt"),
            recursive: false,
            strict: true,
            no_eoi: false,
            lazy_static: false,
        };

        // process optional attrs
        for arg in attr_args_iter {
            match arg {
                NestedMeta::Meta(Meta::NameValue(MetaNameValue {
                    path,
                    eq_token: _,
                    lit,
                })) => {
                    let attr_name = path
                        .get_ident()
                        .unwrap_or_else(|| abort!(path, "Invalid argument to pest_test_gen macro"))
                        .to_string();
                    match attr_name.as_str() {
                        "dir" => {
                            let mut path = match lit {
                                Lit::Str(s) => PathBuf::from(s.value()),
                                _ => abort!(lit, "Invalid argument to 'dir' attribute"),
                            };
                            if path.is_relative() {
                                path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path)
                            }
                            args.dir = path
                        }
                        "subdir" => {
                            args.subdir = match lit {
                                Lit::Str(s) => Some(PathBuf::from(s.value())),
                                _ => abort!(lit, "Invalid argument to 'subdir' attribute"),
                            }
                        }
                        "ext" => {
                            args.ext = match lit {
                                Lit::Str(s) => s.value(),
                                _ => abort!(lit, "Invalid argument to 'ext' attribute"),
                            }
                        }
                        "recursive" => {
                            args.recursive = match lit {
                                Lit::Bool(b) => b.value,
                                _ => abort!(lit, "Invalid argument to 'recursive' attribute"),
                            }
                        }
                        "strict" => {
                            args.strict = match lit {
                                Lit::Bool(b) => b.value,
                                _ => abort!(lit, "Invalid argument to 'strict' attribute"),
                            }
                        }
                        "no_eoi" => {
                            args.no_eoi = match lit {
                                Lit::Bool(b) => b.value,
                                _ => abort!(lit, "Invalid argument to 'strict' attribute"),
                            }
                        }
                        "lazy_static" => {
                            args.lazy_static = match lit {
                                Lit::Bool(b) => b.value,
                                _ => abort!(lit, "Invalid argument to 'lazy_static' attribute"),
                            }
                        }
                        _ => abort!(path, "Invalid argument to pest_test_gen macro"),
                    }
                }
                NestedMeta::Meta(Meta::List(MetaList {
                    path,
                    paren_token: _,
                    nested,
                })) => {
                    let attr_name = path
                        .get_ident()
                        .unwrap_or_else(|| abort!(path, "Invalid argument to pest_test_gen macro"))
                        .to_string();
                    if attr_name == "skip_rule" {
                        for rule_meta in nested {
                            match rule_meta {
                                NestedMeta::Lit(Lit::Str(s)) => {
                                    let rule_name = s.value();
                                    args.skip_rules
                                        .push(Ident::new(rule_name.as_ref(), Span::call_site()));
                                    // if EOI is added manually, don't add it again automatically
                                    if rule_name == "EOI" {
                                        args.no_eoi = true;
                                    }
                                }
                                _ => abort!(rule_meta, "Invalid skip_rule item"),
                            }
                        }
                    } else {
                        abort!(path, "Invalid argument to pest_test_gen macro");
                    }
                }
                _ => abort!(arg, "Invalid argument to pest_test_gen macro"),
            }
        }

        args
    }

    fn iter_tests(&self) -> impl Iterator<Item = String> + '_ {
        let dir = self
            .subdir
            .as_ref()
            .map(|subdir| Cow::Owned(self.dir.join(subdir)))
            .unwrap_or(Cow::Borrowed(&self.dir));
        let mut walker = WalkDir::new(dir.as_ref());
        if !self.recursive {
            walker = walker.max_depth(1);
        }
        walker
            .into_iter()
            .filter_map(|entry| entry.ok())
            .filter(|entry| {
                let path = entry.path();
                if path.is_dir() {
                    false
                } else if self.ext == "" {
                    path.extension().is_none()
                } else {
                    entry.path().extension().map(|s| s.into()) == Some(self.ext.as_ref())
                }
            })
            .map(move |entry| {
                entry
                    .path()
                    .strip_prefix(dir.as_ref())
                    .expect("Error getting relative path of {:?}")
                    .with_extension("")
                    .as_os_str()
                    .to_str()
                    .unwrap()
                    .to_owned()
            })
    }
}

// fn path(path: &[&str], arguments: PathArguments) -> Path {
//     let mut segments: Punctuated<PathSegment, Colon2> = Punctuated::new();
//     for seg in path {
//         segments.push_value(PathSegment {
//             ident: Ident::new(seg, Span::call_site()),
//             arguments,
//         })
//     }
//     Path {
//         leading_colon: None,
//         segments,
//     }
// }

fn rule_variant(rule_path: &Path, variant_ident: Ident) -> Path {
    let mut path = rule_path.clone();
    path.segments.push(PathSegment {
        ident: variant_ident,
        arguments: PathArguments::None,
    });
    path
}

fn add_tests(module: &mut ItemMod, args: &Args) {
    let (_, content) = module.content.get_or_insert_with(|| Default::default());

    let test_dir = args.dir.as_os_str().to_str().unwrap().to_owned();
    let test_ext = args.ext.clone();
    let parser_path = &args.parser_path;
    let rule_path = &args.rule_path;
    let rule_ident = &args.rule_ident;
    let mut skip_rules: Vec<Path> = args
        .skip_rules
        .iter()
        .map(|ident| rule_variant(rule_path, ident.clone()))
        .collect();
    if !args.no_eoi {
        skip_rules.push(rule_variant(
            rule_path,
            Ident::new("EOI", Span::call_site()),
        ));
    }

    if args.lazy_static {
        // let tokens = quote! {
        //     static ref TESTER: pest_test::PestTester<#rule_path, #parser_path> =
        //         PestTester::from_defaults(#rule_path::#rule_ident);
        // };
        // content.push(Item::Macro(ItemMacro {
        //     attrs: Vec::default(),
        //     ident: None,
        //     mac: Macro {
        //         path: path(&["lazy_static", "lazy_static"], PathArguments::None),
        //         bang_token: Bang::default(),
        //         delimiter: MacroDelimiter::Brace(Brace::default()),
        //         tokens,
        //     },
        //     semi_token: None,
        // }));
        let lazy_static_tokens = quote! {
            lazy_static::lazy_static! {
                static ref TESTER: pest_test::PestTester<#rule_path, #parser_path> =
                    pest_test::PestTester::new(
                        #test_dir,
                        #test_ext,
                        #rule_path::#rule_ident,
                        std::collections::HashSet::from([#(#skip_rules),*])
                    );
            }
        };
        let item: Item = match syn::parse2(lazy_static_tokens) {
            Ok(item) => item,
            Err(err) => abort_call_site!(format!("Error generating lazy_static block: {:?}", err)),
        };
        content.push(item);
    }

    for test_name in args.iter_tests() {
        let fn_name = format_ident!("test_{}", test_name);
        let fn_tokens = if args.lazy_static {
            quote! {
                #[test]
                fn #fn_name() -> Result<(), pest_test::TestError<#rule_path>> {
                    let res = (*TESTER).evaluate_strict(#test_name);
                    if let Err(pest_test::TestError::Diff { ref diff }) = res {
                        // TODO: detect value of --color option to cargo-test
                        diff.print_test_result(true).unwrap();
                    }
                    res
                }
            }
        } else {
            quote! {
                #[test]
                fn #fn_name() -> Result<(), pest_test::TestError<#rule_path>> {
                    let tester = pest_test::PestTester::new(
                        #test_dir,
                        #test_ext,
                        #rule_path::#rule_ident,
                        std::collections::HashSet::from([#(#skip_rules),*])
                    );
                    let res = tester.evaluate_strict(#test_name);
                    if let Err(pest_test::TestError::Diff { ref diff }) = res {
                        // TODO: detect value of --color option to cargo-test
                        diff.print_test_result(true).unwrap();
                    }
                    res
                }
            }
        };
        let item: Item = match syn::parse2(fn_tokens) {
            Ok(item) => item,
            Err(err) => {
                abort_call_site!(format!("Error generating test fn {}: {:?}", test_name, err))
            }
        };
        content.push(item);
        // let result_generics: Punctuated<GenericArgument, Comma> = Punctuated::new();
        // result_generics.push(GenericArgument::Type(Type::Tuple(TypeTuple {
        //     paren_token: Paren::default(),
        //     elems: Punctuated::new(),
        // })));
        // result_generics.push(GenericArgument::Type(Type::Path(TypePath {
        //     qself: None,
        //     path: path(&["pest_test", "TestError"], PathArguments::None),
        // })));
        // let sig = Signature {
        //     constness: None,
        //     asyncness: None,
        //     unsafety: None,
        //     abi: None,
        //     fn_token: Fn::default(),
        //     ident: Ident::new(format!("test_{}", test_name).as_ref(), Span::call_site()),
        //     generics: Generics::default(),
        //     paren_token: Paren::default(),
        //     inputs: Punctuated::new(),
        //     variadic: None,
        //     output: ReturnType::Type(
        //         RArrow::default(),
        //         Box::new(Type::Path(TypePath {
        //             qself: None,
        //             path: path(
        //                 &["core", "result", "Result"],
        //                 PathArguments::AngleBracketed(AngleBracketedGenericArguments {
        //                     colon2_token: None,
        //                     lt_token: Lt::default(),
        //                     args: result_generics,
        //                     gt_token: Gt::default(),
        //                 }),
        //             ),
        //         })),
        //     ),
        // };
        // let rhs = if args.lazy_static {
        //     // (*PEST_TESTER)
        // } else {
        //     // PestTester::new()
        // };
        // let args: Punctuated<Expr, Comma> = Punctuated::new();
        // args.push(Expr::Lit(ExprLit {
        //     attrs: Vec::default(),
        //     lit: Lit::Str(LitStr::new(test_name.as_ref(), Span::call_site())),
        // }));
        // content.push(Item::Fn(ItemFn {
        //     attrs: Vec::default(),
        //     vis: Visibility::Inherited,
        //     sig,
        //     block: Box::new(Block {
        //         brace_token: Brace::default(),
        //         stmts: vec![
        //             Stmt::Semi(
        //                 Expr::Let(ExprLet {
        //                     attrs: Vec::default(),
        //                     let_token: Let::default(),
        //                     pat: Pat::Ident(PatIdent {
        //                         attrs: Vec::default(),
        //                         by_ref: None,
        //                         mutability: None,
        //                         ident: Ident::new("tester", Span::call_site()),
        //                         subpat: None,
        //                     }),
        //                     eq_token: Eq::default(),
        //                     expr: Box::new(rhs),
        //                 }),
        //                 Semi::default(),
        //             ),
        //             Stmt::Expr(Expr::MethodCall(ExprMethodCall {
        //                 attrs: Vec::default(),
        //                 receiver: Box::new(Expr::Path(ExprPath {
        //                     attrs: Vec::default(),
        //                     qself: None,
        //                     path: path(&[test_name.as_ref()], PathArguments::None),
        //                 })),
        //                 dot_token: Dot::default(),
        //                 method: Ident::new("evaluate_strict", Span::call_site()),
        //                 turbofish: None,
        //                 paren_token: Paren::default(),
        //                 args,
        //             })),
        //         ],
        //     }),
        // }))
    }
}

/// When added to a test module, adds test functions for pest-test test cases. Must come before
/// the `#[cfg(test)]` attribute. If you specify `lazy_static = true` then a singleton `PestTester`
/// is created and used by all the generated test functions (dependency on `lazy_static` is
/// required), otherwise a separate instance is created for each test.
///
/// Arguments:
/// * <parser type>: (required) the full path to the struct you defined that derives `pest::Parser`,
///   e.g. `mycrate::parser::MyParser`.
/// * <rule type>: (required) the full path to the `Rule` enum, e.g. `mycrate::parser::Rule`.
/// * <rule name>: (required) the name of the `Rule` variant from which to start parsing.
/// * skip_rules: (optional) a list of rules to skip when parsing; by default `Rule::EOI` is
///   skipped unless `no_eoi = true`.
/// * no_eoi: (optional) there is no `Rule::EOI` - don't automatically add it to `skip_rules`.
/// * dir: (optional) the root directory where pest test cases are found; defaults to 'tests/pest'.
/// * subdir: (optional) the subdirectory under `tests/pest` in which to look for test cases;
///   defaults to "".
/// * ext: (optional) the file extension of pest test cases; defaults to "txt".
/// * recursive: (optional) whether to search for tests cases recursively under `{dir}/{subdir}`;
///   defaults to `false`.
/// * strict: (optional) whether to enforce that terminal node values must match between the
///   expected and actual parse trees; defaults to `true`.
/// * lazy_static: (optional) whether to create a singleton `PestTester` - requires dependency on
///   `lazy_static`; defaults to `false`.
///
/// Example:
/// use pest_test_gen;
///
/// #[pest_tests(
///     mycrate::parser::MyParser,
///     mycrate::parser::Rule,
///     "root_rule",
///     skip_rules = (mycrate::parser::Rule::comment),
///     subdir = "foo",
///     recursive = true,
///     lazy_static = true
/// )]
/// #[cfg(test)]
/// mod parser_tests {}
#[proc_macro_attribute]
#[proc_macro_error]
pub fn pest_tests(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = Args::from(parse_macro_input!(attr as AttributeArgs));
    let mut module = match parse_macro_input!(item as Item) {
        Item::Mod(module) => module,
        other => abort!(
            other,
            "The pest_test_gen macro may only be used as an attribute on a module"
        ),
    };
    add_tests(&mut module, &args);
    module.to_token_stream().into()
}
