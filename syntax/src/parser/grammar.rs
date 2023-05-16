mod expressions;
mod items;
mod statements;

pub(super) use expressions::*;
pub(super) use items::*;
pub(super) use statements::*;

use super::*;

pub(super) fn attrs(p: &mut Parser) -> Checkpoint {
    let attr_checkpoint = p.checkpoint();
    let mut attr_seen = AttrFlags::empty();
    p.start_node(ATTRS, |p| loop {
        match p.current() {
            T![pure] => {
                if attr_seen.is_pure() {
                    p.error_help("repeated pure attr", "consider removing one of them");
                }
                attr_seen.insert(AttrFlags::PURE);
                p.start_node(ATTR, |p| p.bump());
            }
            T![ghost] => {
                if attr_seen.is_ghost() {
                    p.error_help("repeated ghost attr", "consider removing one of them");
                }
                attr_seen.insert(AttrFlags::GHOST);
                p.start_node(ATTR, |p| p.bump());
            }
            _ => break,
        }
    });
    attr_checkpoint
}

fn name(p: &mut Parser) {
    p.start_node(NAME, |p| match p.current() {
        T![ident] | T![self] => p.bump(),
        EOF => p.unexpected_eof(),
        _ => p.error("expected a name"),
    });
}
fn name_ref(p: &mut Parser) {
    p.start_node(NAME_REF, |p| match p.current() {
        T![ident] | T![self] => p.bump(),
        EOF => p.unexpected_eof(),
        _ => p.error("expected a name"),
    });
}

fn param_list(p: &mut Parser) {
    p.start_node(PARAM_LIST, |p| {
        if p.at(T!['(']) {
            p.bump();
        } else {
            p.error("consider adding parameters here");
        }

        comma_sep(
            p,
            |t| t == T![')'],
            |p| {
                let attrs_checkpoint = attrs(p);
                if p.at(T![ident]) {
                    p.start_node_at(attrs_checkpoint, PARAM, |p| {
                        name(p);
                        if p.at(T![:]) {
                            p.bump();
                            ty(p);
                        }
                    });
                }

                ControlFlow::Continue(())
            },
        );

        p.expect(T![')']);
    });
}

fn ty(p: &mut Parser) {
    if p.at(T![&]) {
        p.start_node(REF_TYPE, |p| {
            p.bump();

            if p.at(T![mut]) {
                p.bump();
            }
            ty(p);
        });
        return;
    } else if p.at(T![mut]) {
        p.start_node(REF_TYPE, |p| {
            p.error("'mut' is only allowed on references. add '&' here");
            p.bump();
            ty(p);
        });
        return;
    }

    if p.at(T![ghost]) {
        p.start_node(GHOST_TYPE, |p| {
            p.bump();
            ty(p);
        });
        return;
    }

    if p.at(T!['[']) {
        p.start_node(LIST_TYPE, |p| {
            p.bump();
            ty(p);
            p.expect(T![']']);
        });
        return;
    }

    if p.at(T![?]) {
        p.start_node(OPTIONAL, |p| {
            p.bump();
            ty(p);
        });
        return;
    }

    match p.current() {
        T![ident] => {
            p.start_node(NAMED_TYPE, |p| {
                name(p);
                generic_arg_list_opt(p);
            });
        }
        T![int] | T![bool] => p.start_node(PRIMITIVE, |p| p.bump()),
        _ => p.error("specify the type here"),
    }
}

fn generic_arg_list_opt(p: &mut Parser) {
    if p.at(T![<]) {
        p.start_node(GENERIC_ARG_LIST, |p| {
            p.bump();
            comma_sep(
                p,
                |t| t == T![>],
                |p| {
                    if p.at(T![>]) {
                        ControlFlow::Break(())
                    } else {
                        p.start_node(GENERIC_ARG, ty);
                        ControlFlow::Continue(())
                    }
                },
            );
            p.expect(T![>]);
        });
    }
}

fn comma_expr(p: &mut Parser, loc: Location) {
    loop {
        match p.current() {
            t if is_start_of_expr(t) => {
                let mut finished = false;
                p.start_node(COMMA_EXPR, |p| {
                    expr(p, loc);

                    if p.at(T![,]) {
                        p.bump()
                    } else {
                        finished = true
                    }
                });
                if finished {
                    break;
                }
            }
            _ => break,
        }
    }
}

fn arg_list(p: &mut Parser) {
    p.start_node(ARG_LIST, |p| {
        p.expect(T!['(']);

        comma_sep(
            p,
            |t| t == T![')'],
            |p| {
                p.start_node(ARG, |p| {
                    expr(p, Location::NONE);
                });
                ControlFlow::Continue(())
            },
        );

        p.expect(T![')']);
    });
}

fn comma_sep<S, F>(p: &mut Parser, terminator: S, mut f: F)
where
    S: Fn(SyntaxKind) -> bool,
    F: FnMut(&mut Parser) -> ControlFlow<()>,
{
    #[derive(Debug, PartialEq)]
    enum LastThing {
        Comma,
        Item,
        Nothing,
    }
    let mut last = LastThing::Nothing;

    loop {
        match p.current() {
            T![,] => {
                match last {
                    LastThing::Comma => {
                        p.error_help("repeated comma", "delete one of them");
                        p.bump();
                    }
                    LastThing::Item => p.bump(),
                    LastThing::Nothing => {
                        p.error_help("comma before first parameter", "add a parameter before");
                        p.bump();
                    }
                }
                last = LastThing::Comma;
            }
            t if terminator(t) => break,
            T!['}'] => {
                p.error("unmatched '}'");
                break;
            }
            T!['{'] => {
                p.error("unexpected '{'");
                break;
            }
            EOF => {
                p.unexpected_eof();
                break;
            }
            _ => {
                let before = p.current();
                if last == LastThing::Item {
                    p.error("missing ','")
                }
                match f(p) {
                    ControlFlow::Continue(_) => {}
                    ControlFlow::Break(_) => break,
                }
                last = LastThing::Item;
                if before == p.current() {
                    p.bump();
                }
            }
        }
    }
}
