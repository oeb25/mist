use super::*;

#[derive(Debug, Clone, Copy)]
pub enum BlockLike {
    Block,
    NotBolck,
}

pub fn expr(p: &mut Parser, loc: Location) -> Option<BlockLike> {
    expr_bp(p, loc, 0)
}
fn expr_bp(p: &mut Parser, loc: Location, min_bp: u8) -> Option<BlockLike> {
    let mut block_like = BlockLike::NotBolck;
    let lhs = p.checkpoint();
    match p.current() {
        T![false] | T![true] => p.start_node(LITERAL, |p| p.bump()),
        T!['{'] => {
            block(p);
            block_like = BlockLike::Block;
        }
        T![return] => {
            p.start_node(RETURN_EXPR, |p| {
                p.bump();

                if is_start_of_expr(p.current()) {
                    let _ = expr(p, Location::NONE);
                }
            });
        }
        T![result] => p.start_node(RESULT_EXPR, |p| p.bump()),
        T![ident] | T![self] => {
            let checkpoint = p.checkpoint();
            name_ref(p);

            match p.current() {
                T!['{'] if !loc.contains(Location::NO_STRUCT) => {
                    p.start_node_at(checkpoint, STRUCT_EXPR, |p| {
                        p.expect(T!['{']);

                        comma_sep(
                            p,
                            |t| t == T!['}'],
                            |p| match p.current() {
                                T![ident] => {
                                    p.start_node(STRUCT_EXPR_FIELD, |p| {
                                        name_ref(p);
                                        p.expect(T![:]);
                                        expr_bp(p, Location::NONE, 0);
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
                _ => p.wrap_checkpoint_in(checkpoint, IDENT_EXPR),
            }
        }
        T![null] => p.start_node(NULL_EXPR, |p| p.bump()),
        INT_NUMBER => p.start_node(LITERAL, |p| p.bump()),
        T!['['] => {
            p.start_node(LIST_EXPR, |p| {
                p.bump();
                comma_sep(
                    p,
                    |t| t == T![']'],
                    |p| {
                        p.start_node(COMMA_EXPR, |p| {
                            let _ = expr_bp(p, Location::NONE, 0);
                        });
                        ControlFlow::Continue(())
                    },
                );
                p.expect(T![']']);
            });
        }
        T!['('] => {
            p.start_node(PAREN_EXPR, |p| {
                p.bump();
                expr_bp(p, Location::NONE, 0);
                p.expect(T![')']);
            });
        }
        T![if] => {
            if_expr(p);
            block_like = BlockLike::Block;
        }
        T![while] => {
            while_expr(p);
            block_like = BlockLike::Block;
        }
        T![for] => {
            for_expr(p);
            block_like = BlockLike::Block;
        }
        EOF => {
            p.unexpected_eof();
            return None;
        }
        t => {
            if let Some((op, (), r_bp)) = prefix_binding_power(t) {
                match op {
                    T![&] => {
                        p.start_node(REF_EXPR, |p| {
                            p.bump();

                            if p.at(T![mut]) {
                                p.bump();
                            }

                            expr_bp(p, loc, r_bp);
                        });
                    }
                    T![forall] | T![exists] => {
                        p.start_node(QUANTIFIER_EXPR, |p| {
                            p.start_node(QUANTIFIER, |p| p.bump());

                            if let T!['('] = p.current() {
                                param_list(p);
                            } else {
                                name_in_exprs(p);
                            }

                            expr_bp(p, loc, r_bp);
                        });
                    }
                    _ => {
                        p.start_node(PREFIX_EXPR, |p| {
                            p.bump();

                            expr_bp(p, loc, r_bp);
                        });
                    }
                }
            } else {
                p.error(format!("unknown start of expr: '{t}'"));
                p.bump();
                return None;
            }
        }
    };

    loop {
        if let Some((op, l_bp, ())) = postfix_binding_power(p.current()) {
            if l_bp < min_bp {
                break;
            }

            block_like = BlockLike::NotBolck;

            match op {
                T!['('] => p.start_node_at(lhs, CALL_EXPR, arg_list),
                T!['['] => {
                    p.start_node_at(lhs, INDEX_EXPR, |p| {
                        p.bump();
                        expr(p, Location::NONE);
                        p.expect(T![']']);
                    });
                }
                T![!] => {
                    p.start_node_at(lhs, NOT_NULL_EXPR, |p| p.bump());
                }
                T![.] => {
                    p.start_node_at(lhs, FIELD_EXPR, |p| {
                        p.bump();
                        name_ref(p);
                    });
                }
                _ => todo!(),
            }

            continue;
        }
        if let Some((op, l_bp, r_bp)) = infix_binding_power(p.current()) {
            if l_bp < min_bp {
                break;
            }

            block_like = BlockLike::NotBolck;

            match op {
                T![..] => {
                    p.start_node_at(lhs, RANGE_EXPR, |p| {
                        p.bump();
                        if is_start_of_expr(p.current()) {
                            expr_bp(p, loc, r_bp);
                        }
                    });
                }
                _op => {
                    p.start_node_at(lhs, BIN_EXPR, |p| {
                        p.bump();
                        // eprintln!("normal infix op was: '{op}'");
                        expr_bp(p, loc, r_bp);
                    });
                }
            }
            continue;
        };

        break;
    }

    Some(block_like)
}

pub fn name_in_exprs(p: &mut Parser) {
    p.start_node(NAME_IN_EXPRS, |p| loop {
        name_in_expr(p);
        match p.current() {
            T![,] => p.bump(),
            _ => break,
        }
    })
}

pub fn name_in_expr(p: &mut Parser) {
    p.start_node(NAME_IN_EXPR, |p| {
        name(p);
        p.expect(T![in]);
        expr(p, Location::NO_STRUCT);
    });
}

pub fn if_expr(p: &mut Parser) {
    assert!(p.at(T![if]));
    p.start_node(IF_EXPR, |p| {
        p.bump();

        expr(p, Location::NO_STRUCT);
        block(p);

        if p.at(T![else]) {
            p.bump();
            if p.at(T![if]) {
                if_expr(p);
            } else {
                block(p);
            }
        }
    });
}

pub fn while_expr(p: &mut Parser) {
    assert!(p.at(T![while]));

    p.start_node(WHILE_EXPR, |p| {
        p.bump();

        expr(p, Location::NO_STRUCT);

        let mut seen_decreases = false;

        loop {
            match p.current() {
                T![invariant] | T![inv] => {
                    p.start_node(INVARIANT, |p| {
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

        block(p);
    });
}

pub fn for_expr(p: &mut Parser) {
    assert!(p.at(T![for]));
    p.start_node(FOR_EXPR, |p| {
        p.bump();

        name(p);

        p.expect(T![in]);

        expr(p, Location::NO_STRUCT);

        while let T![invariant] | T![inv] = p.current() {
            p.start_node(INVARIANT, |p| {
                p.bump();
                comma_expr(p, Location::NO_STRUCT);
            });
        }

        block(p);
    });
}

pub fn is_start_of_expr(token: SyntaxKind) -> bool {
    matches!(
        token,
        T![ident]
            | T![self]
            | T![true]
            | T![false]
            | T![null]
            | T![result]
            | T![if]
            | T![while]
            | T![for]
            | T![return]
            | T![forall]
            | T![exists]
            | T![&]
            | T![!]
            | T![-]
            | T!['{']
            | T!['(']
            | T!['[']
            | INT_NUMBER,
    )
}

// TODO: https://github.com/rust-lang/rust-analyzer/blob/20b0ae4afe3f9e4c5ee5fc90586e55f2515f403b/crates/syntax/src/ast/prec.rs

fn prefix_binding_power(op: SyntaxKind) -> Option<(SyntaxKind, (), u8)> {
    match op {
        T![&] | T![!] => Some((op, (), 27)),
        // T![+] |
        T![-] => Some((op, (), 9)),
        T![forall] | T![exists] => Some((op, (), 10)),
        _ => None,
    }
}

fn postfix_binding_power(op: SyntaxKind) -> Option<(SyntaxKind, u8, ())> {
    let (l, r) = match op {
        T![!] => (29, ()),
        T!['['] => (11, ()),
        T!['('] => (11, ()),
        T![.] => (31, ()),
        _ => return None,
    };

    Some((op, l, r))
}

fn infix_binding_power(op: SyntaxKind) -> Option<(SyntaxKind, u8, u8)> {
    let (l, r) = match op {
        T![=] => (2, 1),
        T![&&] => (2, 1),
        T![||] => (2, 1),
        T![==] | T![!=] => (4, 3),
        T![>] | T![<] => (4, 3),
        T![>=] | T![<=] => (4, 3),
        T![..] => (4, 3),
        T![+] | T![-] => (5, 6),
        T![*] | T![/] => (7, 8),
        _ => return None,
    };

    Some((op, l, r))
}
