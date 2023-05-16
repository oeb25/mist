use super::*;

pub fn stmt(p: &mut Parser) -> StatementParsed {
    match p.current() {
        T![let] => let_stmt(p),
        T![assume] => assume_stmt(p),
        T![assert] => assert_stmt(p),
        T![while] => while_stmt(p),
        T![if] => {
            let checkpoint = p.checkpoint();
            // p.start_node(EXPR_STMT, |p| {});
            if_expr(p);
            // p.builder.finish_node();
            return StatementParsed::Expression(checkpoint);
        }
        t if is_start_of_expr(t) => {
            let expr_checkpoint = p.checkpoint();
            expr(p, Location::NONE);

            // if let T![;]) = p.current() {                //     p.builder
            //         .start_node_at(expr_checkpoint, EXPR_STMT.into());
            //     p.bump();
            //     p.builder.finish_node();
            // } else {
            //     // tail expr
            return StatementParsed::Expression(expr_checkpoint);
            // }
        }
        EOF => p.unexpected_eof(),
        _ => {
            if !item_opt(p) {
                p.push_error(
                    None,
                    Some("expected a statement here"),
                    None,
                    ParseErrorKind::Context("statement".to_string()),
                );
                p.bump();
            }
        }
    }

    StatementParsed::Statement
}

pub fn let_stmt(p: &mut Parser) {
    assert!(p.at(T![let]));

    p.start_node(LET_STMT, |p| {
        p.bump();

        name(p);

        if p.at(T![:]) {
            p.bump();
            ty(p);
        }

        if p.at(T![=]) {
            p.bump();
            expr(p, Location::NONE);
        }

        p.semicolon();
    });
}

pub fn assume_stmt(p: &mut Parser) {
    assert!(p.at(T![assume]));

    p.start_node(ASSUME_STMT, |p| {
        p.bump();

        comma_expr(p, Location::NONE);
        p.semicolon();
    });
}

pub fn assert_stmt(p: &mut Parser) {
    assert!(p.at(T![assert]));

    p.start_node(ASSERT_STMT, |p| {
        p.bump();

        comma_expr(p, Location::NONE);
        p.semicolon();
    });
}

pub fn while_stmt(p: &mut Parser) {
    assert!(p.at(T![while]));

    p.start_node(WHILE_STMT, |p| {
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
                            p.bump()
                        } else {
                            expr(p, Location::NO_STRUCT)
                        }
                    });
                }
                _ => break,
            }
        }

        block(p);
    });
}
