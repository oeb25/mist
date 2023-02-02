import * as monaco from "monaco-editor";

export const SYNTAX_TREE_ID = "syntax-tree";

monaco.languages.register({
  id: SYNTAX_TREE_ID,
  extensions: ["syntax-tree"],
  aliases: [],
  mimetypes: ["application/syntax-tree"],
});
monaco.languages.setLanguageConfiguration(SYNTAX_TREE_ID, {
  comments: {
    lineComment: "//",
    blockComment: ["/*", "*/"],
  },
  brackets: [
    ["(", ")"],
    ["{", "}"],
    ["[", "]"],
  ],
  autoClosingPairs: [
    { open: "[", close: "]" },
    { open: "{", close: "}" },
    { open: "(", close: ")" },
    { open: "'", close: "'", notIn: ["string", "comment"] },
    { open: '"', close: '"', notIn: ["string"] },
  ],
  surroundingPairs: [
    { open: "{", close: "}" },
    { open: "[", close: "]" },
    { open: "(", close: ")" },
    { open: '"', close: '"' },
    { open: "'", close: "'" },
  ],
  folding: {
    markers: {
      start: new RegExp("^\\s*#pragma\\s+region\\b"),
      end: new RegExp("^\\s*#pragma\\s+endregion\\b"),
    },
  },
  wordPattern: /[a-zA-Z_@$ΣΛλ][a-zA-Z0-9_]*/,
});
monaco.languages.setMonarchTokensProvider(SYNTAX_TREE_ID, {
  defaultToken: "",
  brackets: [
    { token: "delimiter.curly", open: "{", close: "}" },
    { token: "delimiter.parenthesis", open: "(", close: ")" },
    { token: "delimiter.square", open: "[", close: "]" },
    { token: "delimiter.angle", open: "<", close: ">" },
  ],

  keywords: ["const", "fn", "assume", "assert", "let"],
  operators: [
    "-",
    ",",
    "->",
    ":=",
    "!",
    "!=",
    "(",
    ")",
    "{",
    "}",
    "*",
    "/",
    "^",
    "&&",
    "&",
    "+",
    "<",
    "<=",
    "=",
    ">",
    ">=",
    "||",
    "|",
  ],

  escapes:
    /\\(?:[abfnrtv\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,

  tokenizer: {
    root: [
      [
        /[a-zA-Z_$ΣΛλ][a-zA-Z0-9_]*/,
        {
          cases: {
            "@keywords": "keyword",
            "@operators": "operator",
            "@default": "identifier",
          },
        },
      ],
      { include: "@whitespace" },
      [/[-,:=!*\/&+<>|@.]/, "keyword.operator"],
      [/(\/\/).*$/, "comment"],
      [/[{}()\[\]]/, "@brackets"],
      [/[0-9]+/, "number"],
      [/"/, "string", '@string."'],
      [/'/, "string", "@string.'"],
    ],
    whitespace: [
      [/[ \t\r\n]+/, ""],
      [/\/\*/, "comment", "@comment"],
      [/\/\/.*\\$/, "comment", "@linecomment"],
      [/\/\/.*$/, "comment"],
    ],
    comment: [
      [/[^\/*]+/, "comment"],
      [/\*\//, "comment", "@pop"],
      [/[\/*]/, "comment"],
    ],
    linecomment: [
      [/.*[^\\]$/, "comment", "@pop"],
      [/[^]+/, "comment"],
    ],
    string: [
      [
        /[^\\"'%]+/,
        {
          cases: {
            "@eos": { token: "string", next: "@popall" },
            "@default": "string",
          },
        },
      ],
      [/@escapes/, "string.escape"],
      [/\\./, "string.escape.invalid"],
      [/%[\w ]+%/, "variable"],
      [/%%[\w]+(?!\w)/, "variable"],
      [
        /["']/,
        {
          cases: {
            "$#==$S2": { token: "string", next: "@pop" },
            "@default": "string",
          },
        },
      ],
      [/$/, "string", "@popall"],
    ],
  },
});
