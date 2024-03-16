mod node;

use crate::node::{Span, SrcNode};

use chumsky::{
    prelude::*,
    text::{ident, int, newline},
};
use internment::Intern;

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
enum Keyword {
    All,
    Ascending,
    By,
    Create,
    Delete,
    Descending,
    Detach,
    Exists,
    Limit,
    Match,
    Merge,
    On,
    Optional,
    Order,
    Remove,
    Return,
    Set,
    Skip,
    Where,
    With,
    Union,
    Unwind,
    And,
    As,
    Contains,
    Distinct,
    Ends,
    In,
    Is,
    Not,
    Or,
    Starts,
    Xor,
    False,
    True,
    Null,
    Constraint,
    Do,
    For,
    Require,
    Unique,
    Case,
    When,
    Then,
    Else,
    End,
    Mandatory,
    Scalar,
    Of,
    Add,
    Drop,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Delimiter {
    Paren,
    Brack,
    Brace,
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
enum Token {
    Symbol(Intern<String>),
    String(Intern<String>),
    Integer(i64),
    LessMore,
    MoreEq,
    LessEq,
    More,
    Less,
    Dollar,
    Dot,
    DoubleDot,
    Mul,
    Div,
    Mod,
    Colon,
    Pipe,
    Plus,
    Minus,
    Eq,
    PlusEqual,
    Hat,
    Comma,
    Open(Delimiter),
    Close(Delimiter),

    // ReservedWord
    All,
    Ascending,
    By,
    Create,
    Delete,
    Descending,
    Detach,
    Exists,
    Limit,
    Match,
    Merge,
    On,
    Optional,
    Order,
    Remove,
    Return,
    Set,
    Skip,
    Where,
    With,
    Union,
    Unwind,
    And,
    As,
    Contains,
    Distinct,
    Ends,
    In,
    Is,
    Not,
    Or,
    Starts,
    Xor,
    False,
    True,
    Null,
    Constraint,
    Do,
    For,
    Require,
    Unique,
    Case,
    When,
    Then,
    Else,
    End,
    Mandatory,
    Scalar,
    Of,
    Add,
    Drop,
}

fn ident_to_token(ident: String) -> Token {
    let lower = ident.to_ascii_lowercase();
    match lower.as_str() {
        "all" => Token::All,
        "asc" => Token::Ascending,
        "ascending" => Token::Ascending,
        "by" => Token::By,
        "create" => Token::Create,
        "desc" => Token::Descending,
        "descending" => Token::Descending,
        "detach" => Token::Detach,
        "exists" => Token::Exists,
        "limit" => Token::Limit,
        "match" => Token::Match,
        "merge" => Token::Merge,
        "on" => Token::On,
        "optional" => Token::Optional,
        "order" => Token::Order,
        "remove" => Token::Remove,
        "return" => Token::Return,
        "set" => Token::Set,
        "skip" => Token::Skip,
        "where" => Token::Where,
        "with" => Token::With,
        "union" => Token::Union,
        "unwind" => Token::Unwind,
        "and" => Token::And,
        "as" => Token::As,
        "contains" => Token::Contains,
        "distinct" => Token::Distinct,
        "ends" => Token::Ends,
        "in" => Token::In,
        "is" => Token::Is,
        "not" => Token::Not,
        "or" => Token::Or,
        "starts" => Token::Starts,
        "xor" => Token::Xor,
        "false" => Token::False,
        "true" => Token::True,
        "null" => Token::Null,
        "constraint" => Token::Constraint,
        "do" => Token::Do,
        "for" => Token::For,
        "require" => Token::Require,
        "unique" => Token::Unique,
        "case" => Token::Case,
        "when" => Token::When,
        "then" => Token::Then,
        "else" => Token::Else,
        "end" => Token::End,
        "mandatory" => Token::Mandatory,
        "scalar" => Token::Scalar,
        "of" => Token::Of,
        "add" => Token::Add,
        "drop" => Token::Drop,
        _ => Token::Symbol(Intern::new(lower)),
    }
}

fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> + Clone {
    let escaped_symbolic_name = just('`')
        .ignore_then(filter(|c| *c != '`').repeated())
        .then_ignore(just('"'))
        .collect::<String>()
        .map(Intern::new)
        .map(Token::Symbol);

    // TODO: remove unwrap
    // TODO: add double / real
    let decimal_integer = int(10).map(|s: String| Token::Integer(s.parse().unwrap()));
    let hex_integer = just("0x")
        .ignore_then(int(16))
        .map(|s: String| Token::Integer(i64::from_str_radix(&s, 16).unwrap()));
    let octal_integer = just("0o")
        .ignore_then(int(8))
        .map(|s: String| Token::Integer(i64::from_str_radix(&s, 8).unwrap()));
    let integer = choice((decimal_integer, hex_integer, octal_integer));

    // TODO: add \uxxxx and \uxxxxxxxx UTF-16 / UTF-32
    let escape = just('\\').ignore_then(
        just('\\')
            .or(just('/'))
            .or(just('"'))
            .or(just('b').to('\x08'))
            .or(just('f').to('\x0C'))
            .or(just('n').to('\n'))
            .or(just('r').to('\r'))
            .or(just('t').to('\t')),
    );

    let string = just('"')
        .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
        .then_ignore(just('"'))
        .collect::<String>()
        .map(Intern::new)
        .map(Token::String);

    let ctrl = choice((
        just("<>").to(Token::LessMore),
        just(">=").to(Token::MoreEq),
        just("<=").to(Token::LessEq),
        just('>').to(Token::More),
        just('<').to(Token::Less),
        just('$').to(Token::Dollar),
        just("..").to(Token::DoubleDot),
        just('.').to(Token::Dot),
        just('*').to(Token::Mul),
        just('/').to(Token::Div),
        just('%').to(Token::Mod),
        just(':').to(Token::Colon),
        just('|').to(Token::Pipe),
        just("+=").to(Token::PlusEqual),
        just('+').to(Token::Plus),
        just('-').to(Token::Minus),
        just('=').to(Token::Eq),
        just('^').to(Token::Hat),
        just(',').to(Token::Comma),
    ));

    let delim = choice((
        just('(').to(Token::Open(Delimiter::Paren)),
        just(')').to(Token::Close(Delimiter::Paren)),
        just('[').to(Token::Open(Delimiter::Brack)),
        just(']').to(Token::Close(Delimiter::Brack)),
        just('{').to(Token::Open(Delimiter::Brace)),
        just('}').to(Token::Close(Delimiter::Brace)),
    ));

    let token = choice((
        ctrl,
        delim,
        integer,
        string,
        escaped_symbolic_name,
        ident().map(ident_to_token),
    ));

    let single_line = just("//").then(take_until(newline())).ignored();
    let multi_line = just("/*").then(take_until(just("*/"))).ignored();
    let comment = single_line.or(multi_line).padded();

    token
        .map_with_span(move |tok, span| (tok, span))
        .padded_by(comment.repeated())
        .padded()
        // If we encounter an error, skip and attempt to lex the next character as a token instead
        .recover_with(skip_then_retry_until([]))
        .repeated()
        .collect()
}

pub type Spanned<T> = (T, Span);

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
enum Literal {
    Boolean(bool),
    Null,
    Number(i64),
    String(Intern<String>),
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
enum UnaryOp {
    Positive,
    Negative,
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
enum BinaryOp {
    Eq,
    LessMore,
    LessEq,
    Less,
    MoreEq,
    More,
}

#[derive(Clone, Debug, PartialEq)]
enum Expr {
    Parameter(Intern<String>),
    Literal(Literal),
    ListIndexSingle(SrcNode<Self>),
    ListIndexRange(Option<SrcNode<Self>>, Option<SrcNode<Self>>),
    PropertyLookup(Intern<String>),
}

pub fn nested_parser(
    parser: impl Parser<Token, Spanned<Expr>, Error = Simple<Token>>,
    delimiter: Delimiter,
) -> impl Parser<Token, Spanned<Expr>, Error = Simple<Token>> {
    parser.delimited_by(
        just(Token::Open(delimiter)).ignored(),
        just(Token::Close(delimiter)).ignored(),
    )
}

fn parser() -> impl Parser<Token, Spanned<Expr>, Error = Simple<Token>> + Clone {
    let reserved_word = select! {
        Token::All => Intern::new("all".to_string()),
        Token::Ascending => Intern::new("ascending".to_string()),
        Token::By => Intern::new("by".to_string()),
        Token::Create => Intern::new("create".to_string()),
        Token::Descending => Intern::new("descending".to_string()),
        Token::Detach => Intern::new("detach".to_string()),
        Token::Exists => Intern::new("exists".to_string()),
        Token::Limit => Intern::new("limit".to_string()),
        Token::Match => Intern::new("match".to_string()),
        Token::Merge => Intern::new("merge".to_string()),
        Token::On => Intern::new("on".to_string()),
        Token::Optional => Intern::new("optional".to_string()),
        Token::Order => Intern::new("order".to_string()),
        Token::Remove => Intern::new("remove".to_string()),
        Token::Return => Intern::new("return".to_string()),
        Token::Set => Intern::new("set".to_string()),
        Token::Skip => Intern::new("skip".to_string()),
        Token::Where => Intern::new("where".to_string()),
        Token::With => Intern::new("with".to_string()),
        Token::Union => Intern::new("union".to_string()),
        Token::Unwind => Intern::new("unwind".to_string()),
        Token::And => Intern::new("and".to_string()),
        Token::As => Intern::new("as".to_string()),
        Token::Contains => Intern::new("contains".to_string()),
        Token::Distinct => Intern::new("distinct".to_string()),
        Token::Ends => Intern::new("ends".to_string()),
        Token::In => Intern::new("in".to_string()),
        Token::Is => Intern::new("is".to_string()),
        Token::Not => Intern::new("not".to_string()),
        Token::Or => Intern::new("or".to_string()),
        Token::Starts => Intern::new("starts".to_string()),
        Token::Xor => Intern::new("xor".to_string()),
        Token::False => Intern::new("false".to_string()),
        Token::True => Intern::new("true".to_string()),
        Token::Null => Intern::new("null".to_string()),
        Token::Constraint => Intern::new("constraint".to_string()),
        Token::Do => Intern::new("do".to_string()),
        Token::For => Intern::new("for".to_string()),
        Token::Require => Intern::new("require".to_string()),
        Token::Unique => Intern::new("unique".to_string()),
        Token::Case => Intern::new("case".to_string()),
        Token::When => Intern::new("when".to_string()),
        Token::Then => Intern::new("then".to_string()),
        Token::Else => Intern::new("else".to_string()),
        Token::End => Intern::new("end".to_string()),
        Token::Mandatory => Intern::new("mandatory".to_string()),
        Token::Scalar => Intern::new("scalar".to_string()),
        Token::Of => Intern::new("of".to_string()),
        Token::Add => Intern::new("add".to_string()),
        Token::Drop => Intern::new("drop".to_string()),
    };

    let call = just(Token::Symbol(Intern::new("call".to_string())));
    let yield_ = just(Token::Symbol(Intern::new("yield".to_string())));
    let any_ = just(Token::Symbol(Intern::new("any".to_string())));
    let none = just(Token::Symbol(Intern::new("none".to_string())));
    let single = just(Token::Symbol(Intern::new("single".to_string())));

    let symbolic_name = select! { Token::Symbol(i) => i };
    let variable = symbolic_name;

    // TODO: no whitespace...
    let namespace = symbolic_name.then(just(Token::Dot));
    let procedure_name = namespace.then(symbolic_name);

    let procedure_result_field = symbolic_name;
    let implicit_procedure_invocation = procedure_name;

    let yield_item = procedure_result_field
        .then(just(Token::As))
        .or_not()
        .then(variable);

    let function_name = namespace.then(symbolic_name);

    let schema_name = symbolic_name.or(reserved_word);
    let property_key_name = schema_name;
    let property_lookup = just(Token::Dot)
        .ignore_then(property_key_name)
        .map(Expr::PropertyLookup);

    let rel_type_name = schema_name;
    let label_name = schema_name;

    let parameter = just(Token::Dollar).ignore_then(select! { Token::Symbol(s) => s });

    let boolean_literal = select! {
        Token::True => Expr::Literal(Literal::Boolean(true)),
        Token::False => Expr::Literal(Literal::Boolean(false)),
    };

    let integer_literal = select! {
        Token::Integer(i) => Expr::Literal(Literal::Number(i)),
    };

    let string_literal = select! {
        Token::String(i) => Expr::Literal(Literal::String(i)),
    };

    let count = just(Token::Symbol(Intern::new("count".to_string())))
        .then(just(Token::Open(Delimiter::Paren)))
        .then(just(Token::Mul))
        .then(just(Token::Close(Delimiter::Paren)));

    let range_literal = just(Token::Mul).ignore_then(
        integer_literal
            .then(
                just(Token::DoubleDot)
                    .ignore_then(integer_literal.or_not())
                    .or_not(),
            )
            .or_not(),
    );

    let node_label = just(Token::Colon).then(label_name);
    let node_labels = node_label.then(node_label.repeated());

    let relationship_types = just(Token::Colon).then(rel_type_name).then(
        just(Token::Pipe)
            .then(just(Token::Colon).or_not())
            .then(rel_type_name),
    );

    let null_predicate = just(Token::Is).then(just(Token::Null)).or(just(Token::Is)
        .then(just(Token::Not))
        .then(just(Token::Null)));

    let mut atom = Recursive::declare();

    let expr = recursive({
        let atom = atom.clone();
        move |expr| {
            let list_op = nested_parser(expr, Delimiter::Brack)
                .map_with_span(|e, span| Expr::ListIndexSingle(SrcNode::new(e, span)))
                .or(nested_parser(
                    expr.or_not()
                        .then_ignore(just(Token::DoubleDot))
                        .then(expr.or_not()),
                    Delimiter::Brack,
                )
                .map_with_span(|(a, b), span| {
                    let a = a.map(|x| SrcNode::new(x, span));
                    let b = b.map(|x| SrcNode::new(x, span));
                    Expr::ListIndexRange(a, b)
                }));

            let op = atom
                .then(list_op.or(property_lookup).repeated())
                .then(node_labels.or_not());

            let unary = op.or(just(Token::Plus)
                .to(UnaryOp::Positive)
                .or(just(Token::Minus).to(UnaryOp::Negative))
                .then(op));

            let power = unary.then(just(Token::Hat).ignore_then(unary).repeated());

            let mul_div_mod = power.then(
                just(Token::Mul)
                    .then(power)
                    .or(just(Token::Div).then(power))
                    .or(just(Token::Mod).then(power))
                    .repeated(),
            );

            let add_sub = mul_div_mod.then(
                just(Token::Plus)
                    .then(mul_div_mod)
                    .or(just(Token::Minus).then(mul_div_mod))
                    .repeated(),
            );

            let list_predicate = just(Token::In).then(add_sub);

            let string_predicate = just(Token::Starts)
                .then(just(Token::With))
                .or(just(Token::Ends).then(just(Token::With)))
                .or(just(Token::Contains))
                .then(add_sub);

            let string_list_null_predicate = add_sub.then(
                string_predicate
                    .or(list_predicate)
                    .or(null_predicate)
                    .repeated(),
            );

            let partial_cmp = choice((
                just(Token::Eq)
                    .then(string_list_null_predicate)
                    .to(BinaryOp::Eq),
                just(Token::LessMore)
                    .then(string_list_null_predicate)
                    .to(BinaryOp::LessMore),
                just(Token::Less)
                    .then(string_list_null_predicate)
                    .to(BinaryOp::Less),
                just(Token::LessEq)
                    .then(string_list_null_predicate)
                    .to(BinaryOp::LessEq),
                just(Token::More)
                    .then(string_list_null_predicate)
                    .to(BinaryOp::More),
                just(Token::MoreEq)
                    .then(string_list_null_predicate)
                    .to(BinaryOp::MoreEq),
            ));

            let cmp = string_list_null_predicate.then(partial_cmp.repeated());

            let not = just(Token::Not).repeated().then(cmp);
            let and = not.then(just(Token::And).then(not).repeated());
            let xor = and.then(just(Token::Xor).then(and).repeated());
            let or = xor.then(just(Token::Or).then(xor).repeated());

            or
        }
    });

    let case_alt = just(Token::When)
        .then(expr)
        .then(just(Token::Then))
        .then(expr);
    let case_alt_repeated = case_alt.repeated().at_least(1);
    let case_expr = just(Token::Case)
        .then(case_alt_repeated)
        .or(just(Token::Case).then(expr).then(case_alt_repeated))
        .then(just(Token::Else).then(expr).or_not())
        .then(just(Token::End));

    let id_in_coll = variable.then(just(Token::In)).then(expr);

    let where_ = just(Token::Where).then(expr);
    let limit = just(Token::Limit).then(expr);
    let skip = just(Token::Skip).then(expr);
    let sort_item = expr.then(just(Token::Ascending).or(just(Token::Descending)).or_not());
    let order = just(Token::Order)
        .then(just(Token::By))
        .then(sort_item)
        .then(just(Token::Comma).then(sort_item));

    let explicit_procedure_invocation = procedure_name
        .then(just(Token::Open(Delimiter::Paren)))
        .then(expr.then(just(Token::Comma).then(expr).repeated()).or_not())
        .then(just(Token::Close(Delimiter::Paren)));

    let yield_items = yield_item
        .then(just(Token::Comma).then(yield_item).repeated())
        .then(where_.or_not());

    let in_query_call = call
        .then(explicit_procedure_invocation)
        .then(yield_.then(yield_items).or_not());

    let filter_expr = id_in_coll.then(where_.or_not());

    let list_comprehension = just(Token::Open(Delimiter::Brack))
        .then(filter_expr)
        .then(just(Token::Pipe).then(expr).or_not())
        .then(Token::Close(Delimiter::Brack));

    let quantifier = choice((just(Token::All), any_, none, single))
        .then(just(Token::Open(Delimiter::Paren)))
        .then(filter_expr)
        .then(just(Token::Open(Delimiter::Paren)));

    let list_literal = just(Token::Open(Delimiter::Brack))
        .then(expr.then(just(Token::Comma)).then(expr).repeated().or_not())
        .then(just(Token::Close(Delimiter::Brack)));

    let map_literal = just(Token::Open(Delimiter::Brace))
        .then(
            property_key_name
                .then(just(Token::Colon))
                .then(expr)
                .then(
                    just(Token::Comma)
                        .then(property_key_name)
                        .then(just(Token::Colon))
                        .then(expr)
                        .repeated(),
                )
                .or_not(),
        )
        .then(just(Token::Close(Delimiter::Brace)));

    let properties = map_literal.or(parameter);

    let relationship_detail = just(Token::Open(Delimiter::Brack))
        .then(variable.or_not())
        .then(relationship_types.or_not())
        .then(range_literal.or_not())
        .then(properties.or_not())
        .then(just(Token::Close(Delimiter::Brack)));

    let relationship = choice((
        just(Token::Less)
            .then(just(Token::Minus))
            .then(relationship_detail.or_not())
            .then(just(Token::Minus))
            .then(just(Token::More)),
        just(Token::Less)
            .then(just(Token::Minus))
            .then(relationship_detail.or_not())
            .then(just(Token::Minus)),
        just(Token::Minus)
            .then(relationship_detail.or_not())
            .then(just(Token::Minus))
            .then(just(Token::More)),
        just(Token::Minus)
            .then(relationship_detail.or_not())
            .then(just(Token::Minus)),
    ));

    let node_pattern = just(Token::Open(Delimiter::Paren))
        .then(variable.or_not())
        .then(node_labels.or_not())
        .then(properties.or_not())
        .then(just(Token::Close(Delimiter::Paren)));

    let pattern_element_chain = relationship.then(node_pattern);

    let relationships_pattern = node_pattern.then(pattern_element_chain.repeated().at_least(1));
    let pattern_predicate = relationships_pattern;

    let pattern_comprehension = just(Token::Open(Delimiter::Brack))
        .then(variable.then(just(Token::Eq)).or_not())
        .then(relationships_pattern)
        .then(where_.or_not())
        .then(just(Token::Pipe))
        .then(expr)
        .then(Token::Close(Delimiter::Brack));

    let pattern_element = recursive(|pattern_element| {
        node_pattern
            .then(pattern_element_chain.repeated())
            .or(just(Token::Open(Delimiter::Paren))
                .then(pattern_element)
                .then(just(Token::Close(Delimiter::Paren))))
    });

    let anonymous_pattern_part = pattern_element;
    let pattern_part = variable
        .then(just(Token::Eq))
        .then(anonymous_pattern_part)
        .or(anonymous_pattern_part);
    let pattern = pattern_part.then(just(Token::Comma).then(pattern_part).repeated());

    let match_ = just(Token::Optional)
        .or_not()
        .then(just(Token::Match))
        .then(pattern)
        .then(where_.or_not());
    let unwind = just(Token::Unwind)
        .then(expr)
        .then(just(Token::As))
        .then(variable);

    let reading_clause = choice((match_, unwind, in_query_call));

    let create = just(Token::Create).then(pattern);

    let projection_item = expr.then(just(Token::As)).then(variable).or(expr);
    let projection_items = just(Token::Mul)
        .then(just(Token::Comma).then(projection_item).repeated())
        .or(projection_item.then(just(Token::Comma).then(projection_item).repeated()));
    let projection_body = just(Token::Distinct)
        .or_not()
        .then(projection_items)
        .then(order.or_not())
        .then(skip.or_not())
        .then(limit.or_not());

    let return_ = just(Token::Return).then(projection_body);
    let with = just(Token::With)
        .then(projection_body)
        .then(where_.or_not());

    let delete = just(Token::Detach)
        .or_not()
        .then(just(Token::Delete))
        .then(expr)
        .then(just(Token::Comma).then(expr).repeated());

    let property_expr = atom.then(property_lookup.repeated().at_least(1));

    let remove_item = variable.then(node_labels).or(property_expr);
    let remove = just(Token::Remove)
        .then(remove_item)
        .then(just(Token::Comma).then(remove_item).repeated());

    let set_item = choice((
        property_expr.then(just(Token::Eq)).then(expr),
        variable.then(just(Token::Eq)).then(expr),
        variable.then(just(Token::PlusEqual)).then(expr),
        variable.then(node_labels),
    ));
    let set = just(Token::Set)
        .then(set_item)
        .then(just(Token::Comma).then(set_item).repeated());

    let merge_action = just(Token::On)
        .then(just(Token::Match).or(just(Token::Create)))
        .then(set);
    let merge = just(Token::Merge)
        .then(pattern_part)
        .then(merge_action.repeated());

    let updating_clause = choice((create, merge, delete, set, remove));

    let single_part_query = reading_clause.repeated().then(return_).or(reading_clause
        .repeated()
        .then(updating_clause)
        .then(updating_clause.repeated())
        .then(return_.or_not()));
    let multi_part_query = reading_clause
        .repeated()
        .then(updating_clause)
        .repeated()
        .then(with)
        .repeated()
        .at_least(1)
        .then(single_part_query);

    let single_query = single_part_query.or(multi_part_query);
    let union = just(Token::Union)
        .then(just(Token::All).or_not())
        .then(single_query);
    let regular_query = single_query.then(union.repeated());

    atom.define({
        let existential_subquery = just(Token::Exists)
            .then(just(Token::Open(Delimiter::Brace)))
            .then(regular_query)
            .or(pattern.then(where_.or_not()))
            .then(just(Token::Close(Delimiter::Brace)));

        let function_invocation = function_name
            .then(just(Token::Open(Delimiter::Paren)))
            .then(just(Token::Distinct).or_not())
            .then(expr.then(just(Token::Comma).then(expr)).or_not())
            .then(just(Token::Close(Delimiter::Paren)));

        let parenthesized_expr = just(Token::Open(Delimiter::Paren))
            .then(expr)
            .then(just(Token::Close(Delimiter::Paren)));

        let literal = choice((
            boolean_literal,
            just(Token::Null),
            integer_literal,
            string_literal,
            list_literal,
            map_literal,
        ));

        choice((
            literal,
            parameter,
            case_expr,
            count,
            list_comprehension,
            pattern_comprehension,
            quantifier,
            pattern_predicate,
            parenthesized_expr,
            function_invocation,
            existential_subquery,
            variable,
        ))
    });

    let standalone_call = call
        .then(explicit_procedure_invocation.or(implicit_procedure_invocation))
        .then(yield_.then(just(Token::Mul).or(yield_items)).or_not());

    let query = regular_query.or(standalone_call);

    query
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanity() {
        println!(
            "{:?}",
            lexer().parse("MATCH `aaa dd` > 0x12a /*aa*/ //asdasd\nhello world //a as")
        );
    }
}
