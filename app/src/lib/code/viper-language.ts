import * as monaco from "monaco-editor";

export const VIPER_ID = "viper";

monaco.languages.register({
  id: VIPER_ID,
  extensions: ["vpr"],
  aliases: [],
  mimetypes: ["application/viper"],
});
monaco.languages.setLanguageConfiguration(VIPER_ID, {
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
monaco.languages.setMonarchTokensProvider(VIPER_ID, {
  defaultToken: "",
  brackets: [
    { token: "delimiter.curly", open: "{", close: "}" },
    { token: "delimiter.parenthesis", open: "(", close: ")" },
    { token: "delimiter.square", open: "[", close: "]" },
    { token: "delimiter.angle", open: "<", close: ">" },
  ],

  keywords: [
    "predicate",
    "function",
    "method",
    "returns",
    "assume",
    "assert",
    "var",
    "if",
    "else",
    "requires",
    "ensures",
    "result",
    "macro",
    "forall",
    "exists",
    "while",
    "invariant",
  ],
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
    ";",
    ":",
    "::",
  ],
  tokenizer: {
    root: [
      [
        /[a-zA-Z_@$ΣΛλ][a-zA-Z0-9_]*/,
        {
          cases: {
            "@keywords": "keyword",
            "@operators": "operator",
            "@default": "identifier",
          },
        },
      ],
      { include: "@whitespace" },
      [/[-,:=!*\/&+<>|;.?]/, "keyword.operator"],
      [/(\/\/).*$/, "comment"],
      [/[{}()\[\]]/, "@brackets"],
      [/[0-9]+/, "number"],
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
  },
});
