export interface Token {
  type: string;
  content: TokenStream;
  alias?: string | string[];
}

export type TokenStream = string | Token | Array<string | Token>;

declare const Prism: {
  tokenize(text: string, grammar: unknown): Array<string | Token>;
  languages: Record<string, unknown>;
};
export default Prism;
