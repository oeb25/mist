import * as monaco from "monaco-editor";

export const MINT_ID = "mint";

monaco.languages.register({
  id: MINT_ID,
  extensions: ["mint"],
  aliases: [],
  mimetypes: ["application/mint"],
});
monaco.languages.setLanguageConfiguration(MINT_ID, {
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
monaco.languages.setMonarchTokensProvider(MINT_ID, {
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
      [/[-,:=!*\/&+<>|]/, "keyword.operator"],
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
