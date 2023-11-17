module.exports = grammar({
  name: 'stelt',

  extras: $ => [
    /\s|\\\r?\n/,
    $.comment
  ],

  rules: {
    source_file: $ => repeat($._definition),

    comment: $ => seq('//', /(\\+(.|\r?\n)|[^\\\n])*/),

    _definition: $ => choice(
      $.type_declaration,
      $.function_definition,
      $.definition,
      $.type_definition,
      $.type_alias,
      $.from_import,
      $.import,
      $.typefn,
      $.impl,
    ),

    type_alias: $ => seq(
      "alias",
      "type",
      $.ident,
      "=",
      $.type
    ),

    typefn: $ => seq(
      optional("pub"),
      "typefn",
      $.ident,
      optional($.gen_args),
      "(",
      csv($.ident),
      ")",
      "=",
      $.type
    ),

    impl: $ => seq(
      "impl",
      $.ident,
      optional($.gen_args),
      "(",
      csv($.type),
      ")"
    ),

    from_import: $ => seq(
      "from",
      $.ident,
      "import",
      csv_notrail(seq(
        $.ident,
        optional(seq("as", $.ident))
      ))
    ),

    import: $ => seq(
      "import",
      $.ident,
      repeat(seq(".", $.ident)),
    ),

    type_definition: $ => seq(
      optional("pub"),
      optional("owned"),
      "type",
      field("name", $.ident),
      optional($.gen_args),
      "=",
      $.enum_def
    ),

    gen_args: $ => seq(
      "<",
      csv($.ident),
      ">"
    ),

    enum_def: $ => seq(
      $.type_cons,
      repeat(seq("|", $.type_cons))
    ),

    type_cons: $ => seq(
      optional("pub"),
      optional("unsafe"),
      $.cons_ident,
      optional(seq(
        "(",
        optional(csv($.type)),
        ")"
      ))
    ),

    definition: $ => seq(
      $.expr_ident,
      "=",
      $.expr
    ),

    function_definition: $ => seq(
      $.expr_ident,
      '(',
      optional(csv($.pattern)),
      ')',
      '=',
      $.expr,
      optional(seq(
        "where",
        $.pattern,
        "=",
        $.expr,
        repeat(seq(
          "|",
          $.pattern,
          "=",
          $.expr
        ))
      ))
    ),

    pattern: $ => choice(
      seq("(", optional(csv($.pattern))  ,")"),
      seq("[", optional(csv($.pattern)), "]"),
      prec.right(seq($.pattern, "::", $.pattern)),
      seq(optional("unsafe"), $.cons_ident, optional(seq(
        "(",
        optional(csv($.pattern)),
        ")"
      ))),
      $.ident,
      $.num,
      $.str
    ),

    expr: $ => choice(
      seq(
        "(",
        optional(csv($.expr)),
        ")"
      ),
      seq(
        "let",
        $.pattern,
        "=",
        $.expr,
        "in",
        $.expr
      ),
      seq(
        "if",
        "let",
        $.pattern,
        "=",
        $.expr,
        "then",
        $.expr,
        "else",
        $.expr,
      ),
      seq(
        "if",
        $.expr,
        "then",
        $.expr,
        "else",
        $.expr
      ),
      prec.left(seq(
        "match",
        $.expr,
        "with",
        repeat(seq(
          "|",
          $.pattern,
          ":",
          $.expr
        ))
      )),
      // prec.right(seq(
      //   "|",
      //   optional(csv($.pattern)),
      //   "|",
      //   "->",
      //   $.expr
      // )),
      prec.left(1, seq($.expr, "||", $.expr)),
      prec.left(2, seq($.expr, "&&", $.expr)),
      // prec.left(3, seq($.expr, "|", $.expr)),
      prec.left(4, seq($.expr, "^", $.expr)),
      prec.left(5, seq($.expr, "&", $.expr)),
      prec.left(6, seq($.expr, "==", $.expr)),
      prec.left(6, seq($.expr, "!=", $.expr)),
      prec.left(7, seq($.expr, "<", $.expr)),
      prec.left(7, seq($.expr, ">", $.expr)),
      prec.left(7, seq($.expr, "<=", $.expr)),
      prec.left(7, seq($.expr, ">=", $.expr)),
      prec.left(8, seq($.expr, "::", $.expr)),
      prec.left(9, seq($.expr, "+", $.expr)),
      prec.left(9, seq($.expr, "-", $.expr)),
      prec.left(10, seq($.expr, "*", $.expr)),
      prec.left(10, seq($.expr, "/", $.expr)),
      prec.left(10, seq($.expr, "%", $.expr)),
      prec.left(11, seq($.expr, "**", $.expr)),
      prec.left(12, seq("!", $.expr)),
      prec.left(12, seq("~", $.expr)),
      prec.left(12, seq("-", $.expr)),
      $.call_expr,
      prec.right(13, seq($.expr, ".", $.expr_ident)),
      prec.left(13, seq($.expr, "=>", $.expr_ident, "(", optional(csv($.expr)), ")")),
      $.expr_ident,
      $.num,
      $.str,
      seq("[", optional(csv($.expr)), "]"),
      seq("&", $.expr),
      seq("unsafe", $.expr),
    ),

    call_expr: $ => prec.right(13, seq(field("func", $.expr), "(", optional(csv($.expr)), ")")),

    type_declaration: $ => seq(
      optional("pub"),
      optional("unsafe"),
      optional("extern"),
      field("name", $.expr_ident),
      ":",
      optional(
        seq(
          $.ident,
          "(",
          csv($.type),
          ")",
          repeat(seq(
            "+",
            $.ident,
            "(",
            csv($.type),
            ")",
          )),
          "=>"
        )
      ),
      $.type
    ),

    type: $ => choice(
      "u8",
      "u16",
      "u32",
      "u64",
      "i8",
      "i16",
      "i32",
      "i64",
      "char",
      "bool",
      "()",
      seq("(", csv($.type), ")"),
      seq("[", $.type, "]"),
      field("genvar", seq("'", $.ident)),
      seq($.ident, repeat(seq(".", $.ident)), optional(seq("<", csv($.type), ">"))),
      prec.right(seq($.type, "->", $.type)),
      seq($.type, "?")
    ),

    expr_ident: $ => /[a-zA-Z][a-zA-Z0-9_']*[!?]?/,
    ident: $ => /[a-z_]+/,
    cons_ident: $ =>  /[A-Z][a-zA-Z0-9]*/,
    num: $ => /[0-9]+/,
    str: $ => /"[^"]*"/,
  }
});

function csv_notrail(expr) {
  return seq(expr, repeat(seq(",", expr)));
}

function csv(expr) {
  return seq(expr, repeat(seq(",", expr)), optional(","));
}
