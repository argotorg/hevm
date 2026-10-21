// src/schema.ts
var SchemaError = class extends Error {
  name = "SchemaError";
};
function fail(path, expected, value) {
  throw new SchemaError(`${path || "value"}: expected ${expected}, got ${JSON.stringify(value)?.slice(0, 80)}`);
}
function primitive(name, test) {
  return {
    parse(value, path = "") {
      if (!test(value)) fail(path, name, value);
      return value;
    }
  };
}
var str = primitive("a string", (v) => typeof v === "string");
var num = primitive("a number", (v) => typeof v === "number");
var bool = primitive("a boolean", (v) => typeof v === "boolean");
var unknownValue = primitive("anything", () => true);
function lit(...values) {
  return primitive(`one of ${values.join(", ")}`, (v) => values.includes(v));
}
function nullable(inner) {
  return { parse: (value, path = "") => value === null ? null : inner.parse(value, path) };
}
function optional(inner) {
  return { parse: (value, path = "") => value === void 0 ? void 0 : inner.parse(value, path) };
}
function arr(inner) {
  return {
    parse(value, path = "") {
      if (!Array.isArray(value)) fail(path, "an array", value);
      return value.map((v, i) => inner.parse(v, `${path}[${i}]`));
    }
  };
}
function obj(shape) {
  return {
    shape,
    parse(value, path = "") {
      if (typeof value !== "object" || value === null || Array.isArray(value)) fail(path, "an object", value);
      const record2 = value;
      const out = { ...record2 };
      for (const [k, s] of Object.entries(shape)) {
        out[k] = s.parse(record2[k], path === "" ? k : `${path}.${k}`);
      }
      return out;
    }
  };
}
function record(inner) {
  return {
    parse(value, path = "") {
      if (typeof value !== "object" || value === null || Array.isArray(value)) fail(path, "an object", value);
      return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, inner.parse(v, `${path}.${k}`)]));
    }
  };
}
function oneOf(a, b) {
  return {
    parse(value, path = "") {
      try {
        return a.parse(value, path);
      } catch (e) {
        if (!(e instanceof SchemaError)) throw e;
        return b.parse(value, path);
      }
    }
  };
}

// src/api.ts
var codeLine = obj({ pc: num, op: str, arg: nullable(str), current: bool });
var sourceLine = obj({ line: num, text: str, current: bool });
var sourceView = obj({ file: str, line: num, lines: arr(sourceLine) });
var branchView = obj({ condition: nullable(str), options: arr(str) });
var word = oneOf(obj({ hex: str }), obj({ expr: str }));
var view = obj({
  mode: lit("concrete", "symbolic"),
  step: num,
  status: lit("running", "branch", "halted"),
  result: nullable(obj({ outcome: lit("success", "revert", "failure", "unfinished"), output: nullable(word), problem: nullable(str) })),
  pc: num,
  op: str,
  contract: str,
  codeContract: str,
  depth: num,
  gas: nullable(num),
  codeName: nullable(str),
  code: arr(codeLine),
  stack: arr(word),
  memorySize: num,
  memory: word,
  source: nullable(sourceView),
  generatedCode: bool,
  storage: arr(obj({ address: word, current: bool, initial: lit("known", "unknown"), slots: arr(obj({ slot: word, value: word })) })),
  pathConditions: num,
  branch: nullable(branchView),
  choices: arr(str),
  breakpoints: arr(str),
  message: str,
  output: nullable(str),
  branchMode: lit("solver", "explorer", "checked"),
  simplified: bool,
  warnings: arr(str),
  merging: bool
});
var stats = obj({
  step: num,
  snapshotCount: num,
  counters: obj({
    commands: num,
    commandSecs: num,
    opcodes: num,
    replayedOpcodes: num,
    queries: num,
    querySecs: num,
    branchQueries: num,
    solutionQueries: num,
    fetchQueries: num,
    otherQueries: num,
    branchesOffered: num,
    branchesTaken: num,
    staticDecisions: num,
    staticWrong: num,
    staticMissed: num,
    staticInconclusive: num,
    infeasibleOptions: num,
    breakpointHits: num
  })
});
var inFlightQuery = obj({ secs: num, solving: bool, kind: optional(str), pc: optional(num) });
var queryResultCount = obj({ kind: str, result: str, count: num, waitSecs: num, solveSecs: num });
var hotSpot = obj({ addr: str, pc: num, queries: num, solveSecs: num, forks: num });
var runningProgress = obj({
  running: lit(true),
  elapsedSecs: num,
  phase: obj({ name: str, done: num, total: num }),
  paths: obj({ done: num, partial: num }),
  tasks: num,
  workers: arr(record(unknownValue)),
  queries: obj({ done: num, inFlight: arr(inFlightQuery), byResult: arr(queryResultCount) }),
  hottest: arr(hotSpot),
  phases: arr(record(unknownValue))
});
var progress = oneOf(runningProgress, obj({ running: lit(false) }));
var help = obj({ commands: arr(str), api: arr(str) });
var trace = obj({ trace: str });
var ApiError = class extends Error {
  name = "ApiError";
};
async function request(schema, method, path, body) {
  let response;
  try {
    response = await fetch(path, body === void 0 ? { method } : { method, body });
  } catch (e) {
    throw new ApiError(`cannot reach hevm: ${String(e)}`);
  }
  if (!response.ok) throw new ApiError(`${method} ${path}: ${response.status} ${await response.text()}`);
  try {
    return schema.parse(await response.json());
  } catch (e) {
    throw new ApiError(`${method} ${path} answered unexpectedly, is this the hevm the page came with? ${String(e)}`);
  }
}
var api = {
  state: () => request(view, "GET", "/state"),
  command: (command) => request(view, "POST", "/command", JSON.stringify({ command })),
  stats: () => request(stats, "GET", "/stats"),
  progress: () => request(progress, "GET", "/progress"),
  help: () => request(help, "GET", "/help"),
  trace: async () => (await request(trace, "GET", "/trace")).trace
};

// src/keys.ts
var shortcuts = {
  s: "step",
  n: "next",
  o: "over",
  u: "out",
  c: "continue",
  b: "back",
  B: "back-line",
  r: "restart",
  t: "branch true",
  f: "branch false"
};
function keyAction(press, branchPending) {
  if (press.inInput || press.ctrl) return null;
  if (press.key === ":" || press.key === "/") return { focusConsole: true };
  if (press.key === "?") return { help: true };
  const command = shortcuts[press.key];
  if (command !== void 0) return { run: command };
  if (branchPending && /^[0-9]$/.test(press.key)) return { run: `branch ${press.key}` };
  return null;
}

// src/model.ts
var maxLog = 500;
var initialModel = { view: null, stats: null, progress: null, trace: null, busy: false, log: [] };
function logged(model, ...entries) {
  return [...model.log, ...entries].slice(-maxLog);
}
function update(model, msg) {
  switch (msg.type) {
    case "started":
      return { ...model, busy: true, log: logged(model, { kind: "command", text: `> ${msg.command}` }) };
    case "view": {
      const entries = [];
      if (msg.view.output !== null) entries.push({ kind: "output", text: msg.view.output });
      if (msg.view.message !== "") entries.push({ kind: "message", text: msg.view.message });
      return { ...model, view: msg.view, log: logged(model, ...entries) };
    }
    case "stats":
      return { ...model, stats: msg.stats };
    case "progress":
      return { ...model, progress: msg.progress };
    case "trace":
      return { ...model, trace: msg.trace };
    case "failed":
      return { ...model, log: logged(model, { kind: "error", text: msg.error }) };
    case "note":
      return { ...model, log: logged(model, { kind: "message", text: msg.text }) };
    case "finished":
      return { ...model, busy: false };
  }
}
function pcBreakpoints(view2) {
  const found = /* @__PURE__ */ new Map();
  view2.breakpoints.forEach((b, i) => {
    const m = /^pc (0x[0-9a-f]+)$/.exec(b);
    if (m?.[1] !== void 0) found.set(parseInt(m[1], 16), i);
  });
  return found;
}
function branchArgument(options, index) {
  return options.length === 2 && options[0] === "false" ? options[index] ?? String(index) : String(index);
}
var forward = /* @__PURE__ */ new Set(["step", "next", "over", "out", "continue"]);
var backward = /* @__PURE__ */ new Set(["back", "back-line", "restart"]);
function commandEnabled(view2, command) {
  if (view2 === null) return false;
  if (forward.has(command)) return view2.status === "running";
  if (backward.has(command)) return view2.step > 0;
  return true;
}

// src/vdom.ts
function h(tag, props = {}, ...children) {
  const kids = [];
  for (const c of children) {
    if (c === null || c === void 0 || c === false) continue;
    kids.push(typeof c === "object" ? c : text(String(c)));
  }
  return { tag, props, children: kids };
}
function text(s) {
  return { tag: "#text", props: { text: s }, children: [] };
}
function toDom(node) {
  if (node.tag === "#text") return document.createTextNode(String(node.props["text"] ?? ""));
  const el = document.createElement(node.tag);
  for (const [k, v] of Object.entries(node.props)) {
    if (v === void 0) continue;
    if (k === "onClick" && typeof v === "function") el.addEventListener("click", v);
    else if (typeof v === "string") el.setAttribute(k, v);
  }
  for (const c of node.children) el.append(toDom(c));
  return el;
}
function render(container, nodes) {
  container.replaceChildren(...nodes.map(toDom));
}

// src/vendor/prism.js
(typeof window !== "undefined" ? window : globalThis).Prism = { manual: true };
var _self = typeof window !== "undefined" ? window : typeof WorkerGlobalScope !== "undefined" && self instanceof WorkerGlobalScope ? self : {};
var Prism = function(_self2) {
  var lang = /(?:^|\s)lang(?:uage)?-([\w-]+)(?=\s|$)/i;
  var uniqueId = 0;
  var plainTextGrammar = {};
  var _ = {
    /**
     * By default, Prism will attempt to highlight all code elements (by calling {@link Prism.highlightAll}) on the
     * current page after the page finished loading. This might be a problem if e.g. you wanted to asynchronously load
     * additional languages or plugins yourself.
     *
     * By setting this value to `true`, Prism will not automatically highlight all code elements on the page.
     *
     * You obviously have to change this value before the automatic highlighting started. To do this, you can add an
     * empty Prism object into the global scope before loading the Prism script like this:
     *
     * ```js
     * window.Prism = window.Prism || {};
     * Prism.manual = true;
     * // add a new <script> to load Prism's script
     * ```
     *
     * @default false
     * @type {boolean}
     * @memberof Prism
     * @public
     */
    manual: _self2.Prism && _self2.Prism.manual,
    /**
     * By default, if Prism is in a web worker, it assumes that it is in a worker it created itself, so it uses
     * `addEventListener` to communicate with its parent instance. However, if you're using Prism manually in your
     * own worker, you don't want it to do this.
     *
     * By setting this value to `true`, Prism will not add its own listeners to the worker.
     *
     * You obviously have to change this value before Prism executes. To do this, you can add an
     * empty Prism object into the global scope before loading the Prism script like this:
     *
     * ```js
     * window.Prism = window.Prism || {};
     * Prism.disableWorkerMessageHandler = true;
     * // Load Prism's script
     * ```
     *
     * @default false
     * @type {boolean}
     * @memberof Prism
     * @public
     */
    disableWorkerMessageHandler: _self2.Prism && _self2.Prism.disableWorkerMessageHandler,
    /**
     * A namespace for utility methods.
     *
     * All function in this namespace that are not explicitly marked as _public_ are for __internal use only__ and may
     * change or disappear at any time.
     *
     * @namespace
     * @memberof Prism
     */
    util: {
      encode: function encode(tokens) {
        if (tokens instanceof Token) {
          return new Token(tokens.type, encode(tokens.content), tokens.alias);
        } else if (Array.isArray(tokens)) {
          return tokens.map(encode);
        } else {
          return tokens.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/\u00a0/g, " ");
        }
      },
      /**
       * Returns the name of the type of the given value.
       *
       * @param {any} o
       * @returns {string}
       * @example
       * type(null)      === 'Null'
       * type(undefined) === 'Undefined'
       * type(123)       === 'Number'
       * type('foo')     === 'String'
       * type(true)      === 'Boolean'
       * type([1, 2])    === 'Array'
       * type({})        === 'Object'
       * type(String)    === 'Function'
       * type(/abc+/)    === 'RegExp'
       */
      type: function(o) {
        return Object.prototype.toString.call(o).slice(8, -1);
      },
      /**
       * Returns a unique number for the given object. Later calls will still return the same number.
       *
       * @param {Object} obj
       * @returns {number}
       */
      objId: function(obj2) {
        if (!obj2["__id"]) {
          Object.defineProperty(obj2, "__id", { value: ++uniqueId });
        }
        return obj2["__id"];
      },
      /**
       * Creates a deep clone of the given object.
       *
       * The main intended use of this function is to clone language definitions.
       *
       * @param {T} o
       * @param {Record<number, any>} [visited]
       * @returns {T}
       * @template T
       */
      clone: function deepClone(o, visited) {
        visited = visited || {};
        var clone;
        var id;
        switch (_.util.type(o)) {
          case "Object":
            id = _.util.objId(o);
            if (visited[id]) {
              return visited[id];
            }
            clone = /** @type {Record<string, any>} */
            {};
            visited[id] = clone;
            for (var key in o) {
              if (o.hasOwnProperty(key)) {
                clone[key] = deepClone(o[key], visited);
              }
            }
            return (
              /** @type {any} */
              clone
            );
          case "Array":
            id = _.util.objId(o);
            if (visited[id]) {
              return visited[id];
            }
            clone = [];
            visited[id] = clone;
            /** @type {Array} */
            /** @type {any} */
            o.forEach(function(v, i) {
              clone[i] = deepClone(v, visited);
            });
            return (
              /** @type {any} */
              clone
            );
          default:
            return o;
        }
      },
      /**
       * Returns the Prism language of the given element set by a `language-xxxx` or `lang-xxxx` class.
       *
       * If no language is set for the element or the element is `null` or `undefined`, `none` will be returned.
       *
       * @param {Element} element
       * @returns {string}
       */
      getLanguage: function(element) {
        while (element) {
          var m = lang.exec(element.className);
          if (m) {
            return m[1].toLowerCase();
          }
          element = element.parentElement;
        }
        return "none";
      },
      /**
       * Sets the Prism `language-xxxx` class of the given element.
       *
       * @param {Element} element
       * @param {string} language
       * @returns {void}
       */
      setLanguage: function(element, language) {
        element.className = element.className.replace(RegExp(lang, "gi"), "");
        element.classList.add("language-" + language);
      },
      /**
       * Returns the script element that is currently executing.
       *
       * This does __not__ work for line script element.
       *
       * @returns {HTMLScriptElement | null}
       */
      currentScript: function() {
        if (typeof document === "undefined") {
          return null;
        }
        if ("currentScript" in document && 1 < 2) {
          return (
            /** @type {any} */
            document.currentScript
          );
        }
        try {
          throw new Error();
        } catch (err) {
          var src = (/at [^(\r\n]*\((.*):[^:]+:[^:]+\)$/i.exec(err.stack) || [])[1];
          if (src) {
            var scripts = document.getElementsByTagName("script");
            for (var i in scripts) {
              if (scripts[i].src == src) {
                return scripts[i];
              }
            }
          }
          return null;
        }
      },
      /**
       * Returns whether a given class is active for `element`.
       *
       * The class can be activated if `element` or one of its ancestors has the given class and it can be deactivated
       * if `element` or one of its ancestors has the negated version of the given class. The _negated version_ of the
       * given class is just the given class with a `no-` prefix.
       *
       * Whether the class is active is determined by the closest ancestor of `element` (where `element` itself is
       * closest ancestor) that has the given class or the negated version of it. If neither `element` nor any of its
       * ancestors have the given class or the negated version of it, then the default activation will be returned.
       *
       * In the paradoxical situation where the closest ancestor contains __both__ the given class and the negated
       * version of it, the class is considered active.
       *
       * @param {Element} element
       * @param {string} className
       * @param {boolean} [defaultActivation=false]
       * @returns {boolean}
       */
      isActive: function(element, className, defaultActivation) {
        var no = "no-" + className;
        while (element) {
          var classList = element.classList;
          if (classList.contains(className)) {
            return true;
          }
          if (classList.contains(no)) {
            return false;
          }
          element = element.parentElement;
        }
        return !!defaultActivation;
      }
    },
    /**
     * This namespace contains all currently loaded languages and the some helper functions to create and modify languages.
     *
     * @namespace
     * @memberof Prism
     * @public
     */
    languages: {
      /**
       * The grammar for plain, unformatted text.
       */
      plain: plainTextGrammar,
      plaintext: plainTextGrammar,
      text: plainTextGrammar,
      txt: plainTextGrammar,
      /**
       * Creates a deep copy of the language with the given id and appends the given tokens.
       *
       * If a token in `redef` also appears in the copied language, then the existing token in the copied language
       * will be overwritten at its original position.
       *
       * ## Best practices
       *
       * Since the position of overwriting tokens (token in `redef` that overwrite tokens in the copied language)
       * doesn't matter, they can technically be in any order. However, this can be confusing to others that trying to
       * understand the language definition because, normally, the order of tokens matters in Prism grammars.
       *
       * Therefore, it is encouraged to order overwriting tokens according to the positions of the overwritten tokens.
       * Furthermore, all non-overwriting tokens should be placed after the overwriting ones.
       *
       * @param {string} id The id of the language to extend. This has to be a key in `Prism.languages`.
       * @param {Grammar} redef The new tokens to append.
       * @returns {Grammar} The new language created.
       * @public
       * @example
       * Prism.languages['css-with-colors'] = Prism.languages.extend('css', {
       *     // Prism.languages.css already has a 'comment' token, so this token will overwrite CSS' 'comment' token
       *     // at its original position
       *     'comment': { ... },
       *     // CSS doesn't have a 'color' token, so this token will be appended
       *     'color': /\b(?:red|green|blue)\b/
       * });
       */
      extend: function(id, redef) {
        var lang2 = _.util.clone(_.languages[id]);
        for (var key in redef) {
          lang2[key] = redef[key];
        }
        return lang2;
      },
      /**
       * Inserts tokens _before_ another token in a language definition or any other grammar.
       *
       * ## Usage
       *
       * This helper method makes it easy to modify existing languages. For example, the CSS language definition
       * not only defines CSS highlighting for CSS documents, but also needs to define highlighting for CSS embedded
       * in HTML through `<style>` elements. To do this, it needs to modify `Prism.languages.markup` and add the
       * appropriate tokens. However, `Prism.languages.markup` is a regular JavaScript object literal, so if you do
       * this:
       *
       * ```js
       * Prism.languages.markup.style = {
       *     // token
       * };
       * ```
       *
       * then the `style` token will be added (and processed) at the end. `insertBefore` allows you to insert tokens
       * before existing tokens. For the CSS example above, you would use it like this:
       *
       * ```js
       * Prism.languages.insertBefore('markup', 'cdata', {
       *     'style': {
       *         // token
       *     }
       * });
       * ```
       *
       * ## Special cases
       *
       * If the grammars of `inside` and `insert` have tokens with the same name, the tokens in `inside`'s grammar
       * will be ignored.
       *
       * This behavior can be used to insert tokens after `before`:
       *
       * ```js
       * Prism.languages.insertBefore('markup', 'comment', {
       *     'comment': Prism.languages.markup.comment,
       *     // tokens after 'comment'
       * });
       * ```
       *
       * ## Limitations
       *
       * The main problem `insertBefore` has to solve is iteration order. Since ES2015, the iteration order for object
       * properties is guaranteed to be the insertion order (except for integer keys) but some browsers behave
       * differently when keys are deleted and re-inserted. So `insertBefore` can't be implemented by temporarily
       * deleting properties which is necessary to insert at arbitrary positions.
       *
       * To solve this problem, `insertBefore` doesn't actually insert the given tokens into the target object.
       * Instead, it will create a new object and replace all references to the target object with the new one. This
       * can be done without temporarily deleting properties, so the iteration order is well-defined.
       *
       * However, only references that can be reached from `Prism.languages` or `insert` will be replaced. I.e. if
       * you hold the target object in a variable, then the value of the variable will not change.
       *
       * ```js
       * var oldMarkup = Prism.languages.markup;
       * var newMarkup = Prism.languages.insertBefore('markup', 'comment', { ... });
       *
       * assert(oldMarkup !== Prism.languages.markup);
       * assert(newMarkup === Prism.languages.markup);
       * ```
       *
       * @param {string} inside The property of `root` (e.g. a language id in `Prism.languages`) that contains the
       * object to be modified.
       * @param {string} before The key to insert before.
       * @param {Grammar} insert An object containing the key-value pairs to be inserted.
       * @param {Object<string, any>} [root] The object containing `inside`, i.e. the object that contains the
       * object to be modified.
       *
       * Defaults to `Prism.languages`.
       * @returns {Grammar} The new grammar object.
       * @public
       */
      insertBefore: function(inside, before, insert, root) {
        root = root || /** @type {any} */
        _.languages;
        var grammar = root[inside];
        var ret = {};
        for (var token in grammar) {
          if (grammar.hasOwnProperty(token)) {
            if (token == before) {
              for (var newToken in insert) {
                if (insert.hasOwnProperty(newToken)) {
                  ret[newToken] = insert[newToken];
                }
              }
            }
            if (!insert.hasOwnProperty(token)) {
              ret[token] = grammar[token];
            }
          }
        }
        var old = root[inside];
        root[inside] = ret;
        _.languages.DFS(_.languages, function(key, value) {
          if (value === old && key != inside) {
            this[key] = ret;
          }
        });
        return ret;
      },
      // Traverse a language definition with Depth First Search
      DFS: function DFS(o, callback, type, visited) {
        visited = visited || {};
        var objId = _.util.objId;
        for (var i in o) {
          if (o.hasOwnProperty(i)) {
            callback.call(o, i, o[i], type || i);
            var property = o[i];
            var propertyType = _.util.type(property);
            if (propertyType === "Object" && !visited[objId(property)]) {
              visited[objId(property)] = true;
              DFS(property, callback, null, visited);
            } else if (propertyType === "Array" && !visited[objId(property)]) {
              visited[objId(property)] = true;
              DFS(property, callback, i, visited);
            }
          }
        }
      }
    },
    plugins: {},
    /**
     * This is the most high-level function in Prism’s API.
     * It fetches all the elements that have a `.language-xxxx` class and then calls {@link Prism.highlightElement} on
     * each one of them.
     *
     * This is equivalent to `Prism.highlightAllUnder(document, async, callback)`.
     *
     * @param {boolean} [async=false] Same as in {@link Prism.highlightAllUnder}.
     * @param {HighlightCallback} [callback] Same as in {@link Prism.highlightAllUnder}.
     * @memberof Prism
     * @public
     */
    highlightAll: function(async, callback) {
      _.highlightAllUnder(document, async, callback);
    },
    /**
     * Fetches all the descendants of `container` that have a `.language-xxxx` class and then calls
     * {@link Prism.highlightElement} on each one of them.
     *
     * The following hooks will be run:
     * 1. `before-highlightall`
     * 2. `before-all-elements-highlight`
     * 3. All hooks of {@link Prism.highlightElement} for each element.
     *
     * @param {ParentNode} container The root element, whose descendants that have a `.language-xxxx` class will be highlighted.
     * @param {boolean} [async=false] Whether each element is to be highlighted asynchronously using Web Workers.
     * @param {HighlightCallback} [callback] An optional callback to be invoked on each element after its highlighting is done.
     * @memberof Prism
     * @public
     */
    highlightAllUnder: function(container, async, callback) {
      var env = {
        callback,
        container,
        selector: 'code[class*="language-"], [class*="language-"] code, code[class*="lang-"], [class*="lang-"] code'
      };
      _.hooks.run("before-highlightall", env);
      env.elements = Array.prototype.slice.apply(env.container.querySelectorAll(env.selector));
      _.hooks.run("before-all-elements-highlight", env);
      for (var i = 0, element; element = env.elements[i++]; ) {
        _.highlightElement(element, async === true, env.callback);
      }
    },
    /**
     * Highlights the code inside a single element.
     *
     * The following hooks will be run:
     * 1. `before-sanity-check`
     * 2. `before-highlight`
     * 3. All hooks of {@link Prism.highlight}. These hooks will be run by an asynchronous worker if `async` is `true`.
     * 4. `before-insert`
     * 5. `after-highlight`
     * 6. `complete`
     *
     * Some the above hooks will be skipped if the element doesn't contain any text or there is no grammar loaded for
     * the element's language.
     *
     * @param {Element} element The element containing the code.
     * It must have a class of `language-xxxx` to be processed, where `xxxx` is a valid language identifier.
     * @param {boolean} [async=false] Whether the element is to be highlighted asynchronously using Web Workers
     * to improve performance and avoid blocking the UI when highlighting very large chunks of code. This option is
     * [disabled by default](https://prismjs.com/faq.html#why-is-asynchronous-highlighting-disabled-by-default).
     *
     * Note: All language definitions required to highlight the code must be included in the main `prism.js` file for
     * asynchronous highlighting to work. You can build your own bundle on the
     * [Download page](https://prismjs.com/download.html).
     * @param {HighlightCallback} [callback] An optional callback to be invoked after the highlighting is done.
     * Mostly useful when `async` is `true`, since in that case, the highlighting is done asynchronously.
     * @memberof Prism
     * @public
     */
    highlightElement: function(element, async, callback) {
      var language = _.util.getLanguage(element);
      var grammar = _.languages[language];
      _.util.setLanguage(element, language);
      var parent = element.parentElement;
      if (parent && parent.nodeName.toLowerCase() === "pre") {
        _.util.setLanguage(parent, language);
      }
      var code = element.textContent;
      var env = {
        element,
        language,
        grammar,
        code
      };
      function insertHighlightedCode(highlightedCode) {
        env.highlightedCode = highlightedCode;
        _.hooks.run("before-insert", env);
        env.element.innerHTML = env.highlightedCode;
        _.hooks.run("after-highlight", env);
        _.hooks.run("complete", env);
        callback && callback.call(env.element);
      }
      _.hooks.run("before-sanity-check", env);
      parent = env.element.parentElement;
      if (parent && parent.nodeName.toLowerCase() === "pre" && !parent.hasAttribute("tabindex")) {
        parent.setAttribute("tabindex", "0");
      }
      if (!env.code) {
        _.hooks.run("complete", env);
        callback && callback.call(env.element);
        return;
      }
      _.hooks.run("before-highlight", env);
      if (!env.grammar) {
        insertHighlightedCode(_.util.encode(env.code));
        return;
      }
      if (async && _self2.Worker) {
        var worker = new Worker(_.filename);
        worker.onmessage = function(evt) {
          insertHighlightedCode(evt.data);
        };
        worker.postMessage(JSON.stringify({
          language: env.language,
          code: env.code,
          immediateClose: true
        }));
      } else {
        insertHighlightedCode(_.highlight(env.code, env.grammar, env.language));
      }
    },
    /**
     * Low-level function, only use if you know what you’re doing. It accepts a string of text as input
     * and the language definitions to use, and returns a string with the HTML produced.
     *
     * The following hooks will be run:
     * 1. `before-tokenize`
     * 2. `after-tokenize`
     * 3. `wrap`: On each {@link Token}.
     *
     * @param {string} text A string with the code to be highlighted.
     * @param {Grammar} grammar An object containing the tokens to use.
     *
     * Usually a language definition like `Prism.languages.markup`.
     * @param {string} language The name of the language definition passed to `grammar`.
     * @returns {string} The highlighted HTML.
     * @memberof Prism
     * @public
     * @example
     * Prism.highlight('var foo = true;', Prism.languages.javascript, 'javascript');
     */
    highlight: function(text2, grammar, language) {
      var env = {
        code: text2,
        grammar,
        language
      };
      _.hooks.run("before-tokenize", env);
      if (!env.grammar) {
        throw new Error('The language "' + env.language + '" has no grammar.');
      }
      env.tokens = _.tokenize(env.code, env.grammar);
      _.hooks.run("after-tokenize", env);
      return Token.stringify(_.util.encode(env.tokens), env.language);
    },
    /**
     * This is the heart of Prism, and the most low-level function you can use. It accepts a string of text as input
     * and the language definitions to use, and returns an array with the tokenized code.
     *
     * When the language definition includes nested tokens, the function is called recursively on each of these tokens.
     *
     * This method could be useful in other contexts as well, as a very crude parser.
     *
     * @param {string} text A string with the code to be highlighted.
     * @param {Grammar} grammar An object containing the tokens to use.
     *
     * Usually a language definition like `Prism.languages.markup`.
     * @returns {TokenStream} An array of strings and tokens, a token stream.
     * @memberof Prism
     * @public
     * @example
     * let code = `var foo = 0;`;
     * let tokens = Prism.tokenize(code, Prism.languages.javascript);
     * tokens.forEach(token => {
     *     if (token instanceof Prism.Token && token.type === 'number') {
     *         console.log(`Found numeric literal: ${token.content}`);
     *     }
     * });
     */
    tokenize: function(text2, grammar) {
      var rest = grammar.rest;
      if (rest) {
        for (var token in rest) {
          grammar[token] = rest[token];
        }
        delete grammar.rest;
      }
      var tokenList = new LinkedList();
      addAfter(tokenList, tokenList.head, text2);
      matchGrammar(text2, tokenList, grammar, tokenList.head, 0);
      return toArray(tokenList);
    },
    /**
     * @namespace
     * @memberof Prism
     * @public
     */
    hooks: {
      all: {},
      /**
       * Adds the given callback to the list of callbacks for the given hook.
       *
       * The callback will be invoked when the hook it is registered for is run.
       * Hooks are usually directly run by a highlight function but you can also run hooks yourself.
       *
       * One callback function can be registered to multiple hooks and the same hook multiple times.
       *
       * @param {string} name The name of the hook.
       * @param {HookCallback} callback The callback function which is given environment variables.
       * @public
       */
      add: function(name, callback) {
        var hooks = _.hooks.all;
        hooks[name] = hooks[name] || [];
        hooks[name].push(callback);
      },
      /**
       * Runs a hook invoking all registered callbacks with the given environment variables.
       *
       * Callbacks will be invoked synchronously and in the order in which they were registered.
       *
       * @param {string} name The name of the hook.
       * @param {Object<string, any>} env The environment variables of the hook passed to all callbacks registered.
       * @public
       */
      run: function(name, env) {
        var callbacks = _.hooks.all[name];
        if (!callbacks || !callbacks.length) {
          return;
        }
        for (var i = 0, callback; callback = callbacks[i++]; ) {
          callback(env);
        }
      }
    },
    Token
  };
  _self2.Prism = _;
  function Token(type, content, alias, matchedStr) {
    this.type = type;
    this.content = content;
    this.alias = alias;
    this.length = (matchedStr || "").length | 0;
  }
  Token.stringify = function stringify(o, language) {
    if (typeof o == "string") {
      return o;
    }
    if (Array.isArray(o)) {
      var s = "";
      o.forEach(function(e) {
        s += stringify(e, language);
      });
      return s;
    }
    var env = {
      type: o.type,
      content: stringify(o.content, language),
      tag: "span",
      classes: ["token", o.type],
      attributes: {},
      language
    };
    var aliases = o.alias;
    if (aliases) {
      if (Array.isArray(aliases)) {
        Array.prototype.push.apply(env.classes, aliases);
      } else {
        env.classes.push(aliases);
      }
    }
    _.hooks.run("wrap", env);
    var attributes = "";
    for (var name in env.attributes) {
      attributes += " " + name + '="' + (env.attributes[name] || "").replace(/"/g, "&quot;") + '"';
    }
    return "<" + env.tag + ' class="' + env.classes.join(" ") + '"' + attributes + ">" + env.content + "</" + env.tag + ">";
  };
  function matchPattern(pattern, pos, text2, lookbehind) {
    pattern.lastIndex = pos;
    var match = pattern.exec(text2);
    if (match && lookbehind && match[1]) {
      var lookbehindLength = match[1].length;
      match.index += lookbehindLength;
      match[0] = match[0].slice(lookbehindLength);
    }
    return match;
  }
  function matchGrammar(text2, tokenList, grammar, startNode, startPos, rematch) {
    for (var token in grammar) {
      if (!grammar.hasOwnProperty(token) || !grammar[token]) {
        continue;
      }
      var patterns = grammar[token];
      patterns = Array.isArray(patterns) ? patterns : [patterns];
      for (var j = 0; j < patterns.length; ++j) {
        if (rematch && rematch.cause == token + "," + j) {
          return;
        }
        var patternObj = patterns[j];
        var inside = patternObj.inside;
        var lookbehind = !!patternObj.lookbehind;
        var greedy = !!patternObj.greedy;
        var alias = patternObj.alias;
        if (greedy && !patternObj.pattern.global) {
          var flags = patternObj.pattern.toString().match(/[imsuy]*$/)[0];
          patternObj.pattern = RegExp(patternObj.pattern.source, flags + "g");
        }
        var pattern = patternObj.pattern || patternObj;
        for (var currentNode = startNode.next, pos = startPos; currentNode !== tokenList.tail; pos += currentNode.value.length, currentNode = currentNode.next) {
          if (rematch && pos >= rematch.reach) {
            break;
          }
          var str2 = currentNode.value;
          if (tokenList.length > text2.length) {
            return;
          }
          if (str2 instanceof Token) {
            continue;
          }
          var removeCount = 1;
          var match;
          if (greedy) {
            match = matchPattern(pattern, pos, text2, lookbehind);
            if (!match || match.index >= text2.length) {
              break;
            }
            var from = match.index;
            var to = match.index + match[0].length;
            var p = pos;
            p += currentNode.value.length;
            while (from >= p) {
              currentNode = currentNode.next;
              p += currentNode.value.length;
            }
            p -= currentNode.value.length;
            pos = p;
            if (currentNode.value instanceof Token) {
              continue;
            }
            for (var k = currentNode; k !== tokenList.tail && (p < to || typeof k.value === "string"); k = k.next) {
              removeCount++;
              p += k.value.length;
            }
            removeCount--;
            str2 = text2.slice(pos, p);
            match.index -= pos;
          } else {
            match = matchPattern(pattern, 0, str2, lookbehind);
            if (!match) {
              continue;
            }
          }
          var from = match.index;
          var matchStr = match[0];
          var before = str2.slice(0, from);
          var after = str2.slice(from + matchStr.length);
          var reach = pos + str2.length;
          if (rematch && reach > rematch.reach) {
            rematch.reach = reach;
          }
          var removeFrom = currentNode.prev;
          if (before) {
            removeFrom = addAfter(tokenList, removeFrom, before);
            pos += before.length;
          }
          removeRange(tokenList, removeFrom, removeCount);
          var wrapped = new Token(token, inside ? _.tokenize(matchStr, inside) : matchStr, alias, matchStr);
          currentNode = addAfter(tokenList, removeFrom, wrapped);
          if (after) {
            addAfter(tokenList, currentNode, after);
          }
          if (removeCount > 1) {
            var nestedRematch = {
              cause: token + "," + j,
              reach
            };
            matchGrammar(text2, tokenList, grammar, currentNode.prev, pos, nestedRematch);
            if (rematch && nestedRematch.reach > rematch.reach) {
              rematch.reach = nestedRematch.reach;
            }
          }
        }
      }
    }
  }
  function LinkedList() {
    var head = { value: null, prev: null, next: null };
    var tail = { value: null, prev: head, next: null };
    head.next = tail;
    this.head = head;
    this.tail = tail;
    this.length = 0;
  }
  function addAfter(list, node, value) {
    var next = node.next;
    var newNode = { value, prev: node, next };
    node.next = newNode;
    next.prev = newNode;
    list.length++;
    return newNode;
  }
  function removeRange(list, node, count) {
    var next = node.next;
    for (var i = 0; i < count && next !== list.tail; i++) {
      next = next.next;
    }
    node.next = next;
    next.prev = node;
    list.length -= i;
  }
  function toArray(list) {
    var array = [];
    var node = list.head.next;
    while (node !== list.tail) {
      array.push(node.value);
      node = node.next;
    }
    return array;
  }
  if (!_self2.document) {
    if (!_self2.addEventListener) {
      return _;
    }
    if (!_.disableWorkerMessageHandler) {
      _self2.addEventListener("message", function(evt) {
        var message = JSON.parse(evt.data);
        var lang2 = message.language;
        var code = message.code;
        var immediateClose = message.immediateClose;
        _self2.postMessage(_.highlight(code, _.languages[lang2], lang2));
        if (immediateClose) {
          _self2.close();
        }
      }, false);
    }
    return _;
  }
  var script = _.util.currentScript();
  if (script) {
    _.filename = script.src;
    if (script.hasAttribute("data-manual")) {
      _.manual = true;
    }
  }
  function highlightAutomaticallyCallback() {
    if (!_.manual) {
      _.highlightAll();
    }
  }
  if (!_.manual) {
    var readyState = document.readyState;
    if (readyState === "loading" || readyState === "interactive" && script && script.defer) {
      document.addEventListener("DOMContentLoaded", highlightAutomaticallyCallback);
    } else {
      if (window.requestAnimationFrame) {
        window.requestAnimationFrame(highlightAutomaticallyCallback);
      } else {
        window.setTimeout(highlightAutomaticallyCallback, 16);
      }
    }
  }
  return _;
}(_self);
if (typeof module !== "undefined" && module.exports) {
  module.exports = Prism;
}
if (typeof global !== "undefined") {
  global.Prism = Prism;
}
Prism.languages.clike = {
  "comment": [
    {
      pattern: /(^|[^\\])\/\*[\s\S]*?(?:\*\/|$)/,
      lookbehind: true,
      greedy: true
    },
    {
      pattern: /(^|[^\\:])\/\/.*/,
      lookbehind: true,
      greedy: true
    }
  ],
  "string": {
    pattern: /(["'])(?:\\(?:\r\n|[\s\S])|(?!\1)[^\\\r\n])*\1/,
    greedy: true
  },
  "class-name": {
    pattern: /(\b(?:class|extends|implements|instanceof|interface|new|trait)\s+|\bcatch\s+\()[\w.\\]+/i,
    lookbehind: true,
    inside: {
      "punctuation": /[.\\]/
    }
  },
  "keyword": /\b(?:break|catch|continue|do|else|finally|for|function|if|in|instanceof|new|null|return|throw|try|while)\b/,
  "boolean": /\b(?:false|true)\b/,
  "function": /\b\w+(?=\()/,
  "number": /\b0x[\da-f]+\b|(?:\b\d+(?:\.\d*)?|\B\.\d+)(?:e[+-]?\d+)?/i,
  "operator": /[<>]=?|[!=]=?=?|--?|\+\+?|&&?|\|\|?|[?*/~^%]/,
  "punctuation": /[{}[\];(),.:]/
};
Prism.languages.solidity = Prism.languages.extend("clike", {
  "class-name": {
    pattern: /(\b(?:contract|enum|interface|library|new|struct|using)\s+)(?!\d)[\w$]+/,
    lookbehind: true
  },
  "keyword": /\b(?:_|anonymous|as|assembly|assert|break|calldata|case|constant|constructor|continue|contract|default|delete|do|else|emit|enum|event|external|for|from|function|if|import|indexed|inherited|interface|internal|is|let|library|mapping|memory|modifier|new|payable|pragma|private|public|pure|require|returns?|revert|selfdestruct|solidity|storage|struct|suicide|switch|this|throw|using|var|view|while)\b/,
  "operator": /=>|->|:=|=:|\*\*|\+\+|--|\|\||&&|<<=?|>>=?|[-+*/%^&|<>!=]=?|[~?]/
});
Prism.languages.insertBefore("solidity", "keyword", {
  "builtin": /\b(?:address|bool|byte|u?int(?:8|16|24|32|40|48|56|64|72|80|88|96|104|112|120|128|136|144|152|160|168|176|184|192|200|208|216|224|232|240|248|256)?|string|bytes(?:[1-9]|[12]\d|3[0-2])?)\b/
});
Prism.languages.insertBefore("solidity", "number", {
  "version": {
    pattern: /([<>]=?|\^)\d+\.\d+\.\d+\b/,
    lookbehind: true,
    alias: "number"
  }
});
Prism.languages.sol = Prism.languages.solidity;
var prism_default = Prism;

// src/highlight.ts
function flatten(stream, kind, out) {
  if (typeof stream === "string") out.push({ text: stream, kind });
  else if (Array.isArray(stream)) for (const s of stream) flatten(s, kind, out);
  else flatten(stream.content, `tok-${stream.type}`, out);
}
function solidityLines(lines) {
  const pieces2 = [];
  flatten(prism_default.tokenize(lines.join("\n"), prism_default.languages["solidity"]), null, pieces2);
  const result = [[]];
  for (const p of pieces2) {
    p.text.split("\n").forEach((part, i) => {
      if (i > 0) result.push([]);
      if (part !== "") result[result.length - 1].push({ text: part, kind: p.kind });
    });
  }
  return result;
}
var hexWord = /^0x[0-9a-f]+$/i;
function number(hex2) {
  if (!hexWord.test(hex2)) return [{ text: hex2, kind: null }];
  const v = BigInt(hex2);
  return v > 9n && v < 0x10000n ? [{ text: hex2, kind: "num-hex" }, { text: v.toString(), kind: "num-dec" }] : [{ text: hex2, kind: "num-hex" }];
}
var exprToken = /("(?:[^"\\]|\\.)*")|(\b0x[0-9a-fA-F]+\b)|(\b\d+\b)|([A-Za-z_]\w*:)|(\b[A-Z]\w*)|([()])/g;
var exprKinds = ["expr-str", "num-hex", "expr-num", "expr-field", "expr-ctor", "expr-paren"];
function expr(text2) {
  const out = [];
  let last = 0;
  for (const m of text2.matchAll(exprToken)) {
    if (m.index > last) out.push({ text: text2.slice(last, m.index), kind: null });
    const group = m.slice(1).findIndex((g) => g !== void 0);
    out.push({ text: m[0], kind: exprKinds[group] ?? null });
    last = m.index + m[0].length;
  }
  if (last < text2.length) out.push({ text: text2.slice(last), kind: null });
  return out;
}
function unwrap(text2) {
  if (!text2.startsWith("(") || !text2.endsWith(")")) return text2;
  let depth = 0;
  for (let i = 0; i < text2.length; i++) {
    if (text2[i] === "(") depth++;
    else if (text2[i] === ")") depth--;
    if (depth === 0 && i < text2.length - 1) return text2;
  }
  return text2.slice(1, -1).trimEnd();
}
function shownExpr(text2) {
  return expr(unwrap(text2));
}
function word2(w) {
  return "hex" in w ? number(w.hex) : shownExpr(w.expr);
}
function opcode(op, arg) {
  return arg === null ? [{ text: op, kind: "opcode" }] : [{ text: op, kind: "opcode" }, { text: " ", kind: null }, ...number(arg)];
}
function memoryRows(hex2) {
  const bytes = hex2.replace(/^0x/, "").match(/../g) ?? [];
  const rows = [];
  for (let off = 0; off < bytes.length; off += 16) {
    const row = bytes.slice(off, off + 16);
    const out = [{ text: off.toString(16).padStart(4, "0") + ":", kind: "mem-addr" }];
    row.forEach((b, i) => {
      out.push({ text: i % 4 === 0 ? "  " : " ", kind: null }, { text: b, kind: b === "00" ? "mem-zero" : "mem-byte" });
    });
    const ascii = row.map((b) => {
      const c = parseInt(b, 16);
      return c >= 32 && c < 127 ? String.fromCharCode(c) : ".";
    });
    out.push({ text: "   " + "   ".repeat(16 - row.length), kind: null }, { text: ascii.join(""), kind: "mem-ascii" });
    rows.push(out);
  }
  return rows;
}
function resultText(r) {
  const output = r.output === null ? "" : "hex" in r.output ? r.output.hex === "0x" ? ", returned nothing" : `, returned ${r.output.hex}` : ", returned a symbolic value";
  return r.outcome + output + (r.problem === null ? "" : `: ${r.problem}`);
}

// src/view.ts
var maxValueLines = 12;
function valueBlock(w, copy) {
  if ("hex" in w) return [h("pre", { class: "word" }, ...pieces(word2(w)))];
  const lines = unwrap(w.expr).split("\n");
  const shown = h("pre", { class: "word" }, ...pieces(expr(lines.slice(0, maxValueLines).join("\n"))));
  if (lines.length <= maxValueLines) return [shown];
  return [
    shown,
    h(
      "div",
      { class: "more" },
      `\u2026 ${lines.length - maxValueLines} more lines `,
      h("button", { type: "button", class: "small", title: "copy the whole expression", onClick: () => copy(w.expr) }, "copy")
    )
  ];
}
function hex(n) {
  return "0x" + n.toString(16);
}
function fixed(n, digits) {
  return Number.isInteger(n) ? String(n) : n.toFixed(digits);
}
function pieces(ps) {
  return ps.map((p) => p.kind === null ? p.text : h("span", { class: p.kind }, p.text));
}
var badge = (label, cls) => h("span", { class: `badge ${cls}` }, label);
function statusBar(v) {
  return [
    h("span", { class: "step" }, `Step ${v.step}`),
    badge(v.status, `status-${v.status}`),
    badge(v.mode, "mode"),
    h("span", { class: "where" }, `pc ${hex(v.pc)} `, h("b", {}, v.op)),
    h("span", { class: "meta" }, `depth ${v.depth}`),
    v.gas !== null && h("span", { class: "meta" }, `gas ${v.gas}`),
    h("span", { class: "contract", title: `code of ${v.codeContract}` }, v.contract),
    v.branchMode !== "solver" && badge(`branches: ${v.branchMode}`, "setting"),
    v.merging && badge("merging", "setting"),
    !v.simplified && badge("not simplified", "setting")
  ].filter((n) => n !== false);
}
function codePane(v, run) {
  const breaks = pcBreakpoints(v);
  const header = h("div", { class: "file" }, v.codeName ?? "code", h("span", { class: "code-addr" }, ` at ${v.codeContract}`));
  return [header, ...v.code.map((line) => {
    const bp = breaks.get(line.pc);
    const cls = ["code-line", line.current ? "current" : "", bp !== void 0 ? "has-break" : ""].filter(Boolean).join(" ");
    return h(
      "div",
      {
        class: cls,
        title: bp !== void 0 ? "click to delete the breakpoint" : "click to break here",
        onClick: () => run(bp !== void 0 ? `delete ${bp}` : `break pc ${hex(line.pc)}`)
      },
      h("span", { class: "gutter" }, bp !== void 0 ? "\u25CF" : line.current ? "\u25B6" : ""),
      h("span", { class: "addr" }, hex(line.pc)),
      h("span", { class: "op" }, ...pieces(opcode(line.op, line.arg)))
    );
  })];
}
function sourcePane(v) {
  if (v.source === null) {
    return [
      h(
        "div",
        { class: "empty" },
        v.generatedCode ? "Compiler-generated code, such as ABI decoding or overflow checks: it has no Solidity source. Use 'next' to step to the next source line." : "No source map for this code. Run hevm in the project root, with its build output."
      )
    ];
  }
  const highlighted = solidityLines(v.source.lines.map((l) => l.text));
  return [
    h("div", { class: "file" }, `${v.source.file}:${v.source.line}`),
    ...v.source.lines.map(
      (l, i) => h(
        "div",
        { class: l.current ? "src-line current" : "src-line" },
        h("span", { class: "lineno" }, l.line),
        h("span", { class: "text" }, ...pieces(highlighted[i] ?? []))
      )
    )
  ];
}
function stackPane(v, copy) {
  if (v.stack.length === 0) return [h("div", { class: "empty" }, "empty")];
  return v.stack.map((w, i) => h("div", { class: "stack-item" }, h("span", { class: "index" }, i), h("div", {}, ...valueBlock(w, copy))));
}
function memoryPane(v, run) {
  return [
    h(
      "div",
      { class: "pane-note" },
      `${v.memorySize} bytes`,
      v.memorySize > 128 && " \xB7 first 128 shown ",
      v.memorySize > 128 && h("button", { type: "button", class: "small", onClick: () => run(`memory 0 ${Math.min(v.memorySize, 65536)}`) }, "show all")
    ),
    v.memorySize > 0 && h(
      "pre",
      { class: "memory" },
      ..."hex" in v.memory ? memoryRows(v.memory.hex).flatMap((row, i) => [i > 0 && "\n", ...pieces(row)]) : pieces(shownExpr(v.memory.expr))
    )
  ].filter((n) => n !== false);
}
function branchPane(v, run) {
  if (v.branch === null) {
    return [
      h("div", { class: "empty" }, v.mode === "symbolic" ? "No branch pending." : "Concrete run: no symbolic branches."),
      ...v.choices.length > 0 ? [h("div", { class: "pane-note" }, "Taken so far:"), ...v.choices.map((c) => h("div", { class: "choice" }, c))] : []
    ];
  }
  const { options, condition } = v.branch;
  return [
    h("div", { class: "pane-note" }, "Pick a side: keys t / f, or the option's number"),
    h(
      "div",
      { class: "options" },
      ...options.map((opt, i) => h("button", { type: "button", class: "branch-option", onClick: () => run(`branch ${branchArgument(options, i)}`) }, `${i}: ${opt}`))
    ),
    condition !== null && h("pre", { class: "condition", title: "the branch condition" }, ...pieces(shownExpr(condition)))
  ].filter((n) => n !== false);
}
function storagePane(v, copy) {
  if (v.storage.length === 0) return [h("div", { class: "empty" }, "No storage.")];
  return v.storage.map(
    (st) => h(
      "div",
      { class: st.current ? "store current-store" : "store" },
      h("div", { class: "store-head" }, h("span", { class: "store-addr" }, ..."hex" in st.address ? [st.address.hex] : [st.address.expr]), ` \xB7 initial storage ${st.initial}`),
      ...st.slots.length === 0 ? [h("div", { class: "empty" }, "nothing written")] : st.slots.map((sl) => h("div", { class: "slot" }, h("div", {}, ...valueBlock(sl.slot, copy)), h("div", {}, ...valueBlock(sl.value, copy))))
    )
  );
}
function breakpointList(v, run) {
  if (v.breakpoints.length === 0) return [h("div", { class: "empty" }, "None. Click a line of code, or add one below.")];
  return v.breakpoints.map(
    (b, i) => h("div", { class: "bp" }, h("span", {}, `${i}: ${b}`), h("button", { type: "button", class: "small", title: "delete", onClick: () => run(`delete ${i}`) }, "\u2715"))
  );
}
function warningsPane(v) {
  return v.warnings.map((w) => h("pre", { class: "warning" }, w));
}
function statsRows(s) {
  const c = s.counters;
  return [
    ["opcodes", `${c.opcodes} (${c.replayedOpcodes} replayed going back)`],
    ["commands", `${c.commands} in ${fixed(c.commandSecs, 3)}s`],
    ["solver queries", `${c.queries} in ${fixed(c.querySecs, 3)}s`],
    ["  by kind", `${c.branchQueries} branch \xB7 ${c.solutionQueries} solutions \xB7 ${c.fetchQueries} fetch \xB7 ${c.otherQueries} other`],
    ["branches", `${c.branchesOffered} offered \xB7 ${c.branchesTaken} taken \xB7 ${c.infeasibleOptions} infeasible values hidden`],
    ["static decisions", `${c.staticDecisions} (${c.staticWrong} wrong \xB7 ${c.staticMissed} missed \xB7 ${c.staticInconclusive} unchecked)`],
    ["breakpoint hits", String(c.breakpointHits)],
    ["snapshots", String(s.snapshotCount)]
  ];
}
function statsPane(s) {
  if (s === null) return [h("div", { class: "empty" }, "\u2026")];
  return [h("table", {}, ...statsRows(s).map(([k, val]) => h("tr", {}, h("th", {}, k), h("td", {}, val))))];
}
function progressPane(p, busy) {
  if (p === null || !p.running) return [h("div", { class: "empty" }, busy ? "Working\u2026" : "Idle.")];
  const solving = p.queries.inFlight.filter((q) => q.solving);
  return [
    h("div", { class: busy ? "progress-line busy" : "progress-line" }, busy ? "Working \xB7 " : "", `${p.queries.done} solver queries done`),
    ...solving.map((q) => h("div", { class: "solving" }, `solving ${q.kind ?? "a query"} for ${fixed(q.secs, 1)}s${q.pc !== void 0 ? ` at pc ${hex(q.pc)}` : ""}`)),
    ...p.hottest.length > 0 ? [h("div", { class: "pane-note" }, "Most solver time:")] : [],
    ...p.hottest.slice(0, 5).map((s) => h("div", { class: "hot" }, `pc ${hex(s.pc)} \xB7 ${fixed(s.solveSecs, 2)}s \xB7 ${s.queries} queries`))
  ];
}
function tracePane(trace2) {
  if (trace2 === null) return [h("div", { class: "empty" }, "\u2026")];
  if (trace2.trim() === "") return [h("div", { class: "empty" }, "No calls yet.")];
  return [h("pre", { class: "trace" }, trace2)];
}
function logPane(log) {
  return log.map((e) => h("pre", { class: `log-${e.kind}` }, e.text));
}

// src/app.ts
function byId(id) {
  const node = document.getElementById(id);
  if (node === null) throw new Error(`the page has no #${id}`);
  return node;
}
var App = class {
  model = initialModel;
  history = [];
  historyPos = 0;
  input = byId("command");
  breakInput = byId("break-input");
  async start() {
    this.input.addEventListener("keydown", (e) => this.onConsoleKey(e));
    this.breakInput.addEventListener("keydown", (e) => {
      if (e.key === "Enter" && this.breakInput.value.trim() !== "") {
        this.run(`break ${this.breakInput.value.trim()}`);
        this.breakInput.value = "";
      }
    });
    document.addEventListener("keydown", (e) => this.onKey(e));
    for (const button of document.querySelectorAll("[data-command]")) {
      button.addEventListener("click", () => this.run(button.dataset["command"] ?? ""));
    }
    try {
      this.dispatch({ type: "view", view: await api.state() });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    }
    await this.refreshSide();
  }
  run = (command) => {
    void this.execute(command);
  };
  copy = (text2) => {
    navigator.clipboard.writeText(text2).then(
      () => this.dispatch({ type: "note", text: `Copied ${text2.length} characters.` }),
      (e) => this.dispatch({ type: "failed", error: `Cannot copy: ${String(e)}` })
    );
  };
  dispatch(msg) {
    this.model = update(this.model, msg);
    this.draw();
  }
  async execute(command) {
    if (this.model.busy) {
      this.dispatch({ type: "failed", error: "Still working on the previous command." });
      return;
    }
    this.dispatch({ type: "started", command });
    const poller = window.setInterval(() => void this.poll(), 500);
    try {
      this.dispatch({ type: "view", view: await api.command(command) });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    } finally {
      window.clearInterval(poller);
      this.dispatch({ type: "finished" });
      await this.refreshSide();
    }
  }
  async poll() {
    try {
      this.dispatch({ type: "progress", progress: await api.progress() });
    } catch {
    }
  }
  async refreshSide() {
    try {
      const [stats2, progress2, trace2] = await Promise.all([api.stats(), api.progress(), api.trace()]);
      this.dispatch({ type: "stats", stats: stats2 });
      this.dispatch({ type: "progress", progress: progress2 });
      this.dispatch({ type: "trace", trace: trace2 });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    }
  }
  draw() {
    const m = this.model;
    document.body.classList.toggle("busy", m.busy);
    const v = m.view;
    if (v !== null) {
      render(byId("status"), statusBar(v));
      render(byId("code"), codePane(v, this.run));
      render(byId("source"), sourcePane(v));
      render(byId("stack"), stackPane(v, this.copy));
      render(byId("memory"), memoryPane(v, this.run));
      render(byId("storage"), storagePane(v, this.copy));
      render(byId("branch"), branchPane(v, this.run));
      render(byId("breakpoints"), breakpointList(v, this.run));
      render(byId("warnings-list"), warningsPane(v));
      byId("warnings").hidden = v.warnings.length === 0;
      byId("result").textContent = v.result === null ? "" : resultText(v.result);
      byId("code").querySelector(".current")?.scrollIntoView({ block: "nearest" });
      byId("source").querySelector(".current")?.scrollIntoView({ block: "center" });
    }
    for (const button of document.querySelectorAll("[data-command]")) {
      button.disabled = !commandEnabled(v, button.dataset["command"] ?? "");
    }
    render(byId("stats"), statsPane(m.stats));
    render(byId("progress"), progressPane(m.progress, m.busy));
    render(byId("trace"), tracePane(m.trace));
    const log = byId("log");
    render(log, logPane(m.log));
    log.scrollTop = log.scrollHeight;
  }
  onConsoleKey(e) {
    if (e.key === "Enter") {
      const command = this.input.value.trim();
      this.input.value = "";
      if (command === "") return;
      this.history.push(command);
      this.historyPos = this.history.length;
      this.run(command);
    } else if (e.key === "ArrowUp" && this.historyPos > 0) {
      this.historyPos--;
      this.input.value = this.history[this.historyPos] ?? "";
      e.preventDefault();
    } else if (e.key === "ArrowDown" && this.historyPos < this.history.length) {
      this.historyPos++;
      this.input.value = this.history[this.historyPos] ?? "";
      e.preventDefault();
    } else if (e.key === "Escape") {
      this.input.blur();
    }
  }
  onKey(e) {
    const target = e.target;
    const action = keyAction(
      { key: e.key, ctrl: e.ctrlKey || e.metaKey || e.altKey, inInput: target?.tagName === "INPUT" },
      this.model.view?.branch !== null && this.model.view?.branch !== void 0
    );
    if (action === null) return;
    e.preventDefault();
    if ("run" in action) {
      if (commandEnabled(this.model.view, action.run)) this.run(action.run);
    } else if ("focusConsole" in action) this.input.focus();
    else void this.showHelp();
  }
  async showHelp() {
    const help2 = await api.help();
    const keys = [...Object.entries(shortcuts).map(([k, c]) => `${k}   ${c}`), "0-9 pick that branch option", ":   type a command", "?   this help"];
    const dialog = byId("help");
    render(dialog, [
      h("h2", {}, "Keys"),
      h("pre", {}, keys.join("\n")),
      h("h2", {}, "Commands"),
      h("pre", {}, help2.commands.join("\n")),
      h("p", { class: "pane-note" }, "Click anywhere to close.")
    ]);
    dialog.showModal();
  }
};

// src/main.ts
void new App().start();
