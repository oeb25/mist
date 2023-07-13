use super::*;

pub fn item_opt(p: &mut Parser) -> bool {
    let attrs_checkpoint = attrs(p);

    match p.current() {
        T![fn] => fn_def(p, attrs_checkpoint),
        T![const] => const_def(p, attrs_checkpoint),
        T![struct] => struct_def(p, attrs_checkpoint),
        T![invariant] => type_invariant(p, attrs_checkpoint),
        T![macro] => macro_def(p, attrs_checkpoint),
        T![let] => {
            p.error_help("let found as top-level", "consider using a 'const' instead");
            let_stmt(p);
        }
        _ => return false,
    }
    true
}

pub fn fn_def(p: &mut Parser, attr_checkpoint: Checkpoint) {
    assert!(p.at(T![fn]));
    p.start_node_at(attr_checkpoint, FN, |p| {
        p.bump();

        name(p);
        param_list(p);

        if p.at(T![->]) {
            p.bump();
            ty(p);
        }

        let mut seen_decreases = false;

        loop {
            match p.current() {
                T![requires] | T![req] => {
                    p.start_node(REQUIRES, |p| {
                        p.bump();
                        comma_expr(p, Location::NO_STRUCT);
                    });
                }
                T![ensures] | T![ens] => {
                    p.start_node(ENSURES, |p| {
                        p.bump();
                        comma_expr(p, Location::NO_STRUCT);
                    });
                }
                T![decreases] | T![dec] => {
                    if seen_decreases {
                        // TODO: Report repeated decreases
                    }
                    seen_decreases = true;

                    p.start_node(DECREASES, |p| {
                        p.bump();
                        if p.at(T![_]) {
                            p.bump();
                        } else {
                            expr(p, Location::NO_STRUCT);
                        }
                    });
                }
                _ => break,
            }
        }

        if p.at(T![proof]) {
            p.bump();
        }

        match p.current() {
            // TODO: handle proof without body
            T![;] => p.bump(),
            T!['{'] => block(p),
            _ => p.push_error(
                Some(p.pre_whitespace_span.set_len(1)),
                Some("expected a block"),
                None,
                ParseErrorKind::Context("{".to_string()),
            ),
        }
    });
}

fn const_def(p: &mut Parser, attr_checkpoint: Checkpoint) {
    assert!(p.at(T![const]));
    p.start_node_at(attr_checkpoint, CONST, |p| {
        p.bump();

        name(p);

        let post_span = p.current_span();
        match p.current() {
            T![=] => {
                p.bump();
                expr(p, Location::NONE);
                p.semicolon();
            }
            T![;] => {
                p.semicolon();
            }
            _ => p.push_error(
                Some(post_span),
                Some("expected a value with '=', or ';'"),
                None,
                ParseErrorKind::Context("constant value".to_string()),
            ),
        }
    });
}

fn struct_def(p: &mut Parser, attr_checkpoint: Checkpoint) {
    assert!(p.at(T![struct]));
    p.start_node_at(attr_checkpoint, STRUCT, |p| {
        p.bump();

        name(p);
        generic_param_list_opt(p);

        p.expect(T!['{']);

        comma_sep(
            p,
            |t| t == T!['}'],
            |p| match p.current() {
                T![ident] => {
                    p.start_node(STRUCT_FIELD, |p| {
                        name(p);
                        p.expect(T![:]);
                        ty(p);
                    });
                    ControlFlow::Continue(())
                }

                T![ghost] => {
                    p.start_node(STRUCT_FIELD, |p| {
                        attrs(p);
                        name(p);
                        p.expect(T![:]);
                        ty(p);
                    });
                    ControlFlow::Continue(())
                }
                T!['}'] => ControlFlow::Break(()),
                _ => {
                    p.error("unexpected token");
                    ControlFlow::Break(())
                }
            },
        );

        p.expect(T!['}']);
    });
}

fn type_invariant(p: &mut Parser, attr_checkpoint: Checkpoint) {
    assert!(p.at(T![invariant]));
    p.start_node_at(attr_checkpoint, TYPE_INVARIANT, |p| {
        p.bump();
        generic_param_list_opt(p);
        ty(p);
        generic_arg_list_opt(p);
        block(p);
    });
}

fn macro_def(p: &mut Parser, attr_checkpoint: Checkpoint) {
    assert!(p.at(T![macro]));
    p.start_node_at(attr_checkpoint, MACRO, |p| {
        p.bump();
        name(p);
        param_list(p);
        block(p);
    });
}
