// Which source files a compilation needs: the ones it starts from, and all they import.

/** The paths a Solidity source imports, as written */
export function importsOf(source: string): string[] {
  const code = source.replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*/g, "");
  return [...code.matchAll(/\bimport\s+(?:[^;"']*?\bfrom\s+)?["']([^"']+)["']/g)].map((m) => m[1]!);
}

function normalize(path: string): string {
  const out: string[] = [];
  for (const part of path.split("/")) {
    if (part === "." || part === "") continue;
    if (part === "..") out.pop();
    else out.push(part);
  }
  return (path.startsWith("/") ? "/" : "") + out.join("/");
}

/** solc's source unit name for an import: relative to the importer, else as written, after remappings */
export function resolveImport(importer: string, path: string, remappings: string[] = []): string {
  if (path.startsWith("./") || path.startsWith("../")) {
    return normalize(`${importer.slice(0, importer.lastIndexOf("/") + 1)}${path}`);
  }
  let best: { prefix: string; target: string } | undefined;
  for (const r of remappings) {
    const m = /^(?:([^:=]*):)?([^=]+)=(.*)$/.exec(r);
    if (!m || (m[1] && !importer.startsWith(m[1]))) continue;
    if (path.startsWith(m[2]!) && (!best || m[2]!.length > best.prefix.length)) best = { prefix: m[2]!, target: m[3]! };
  }
  return best ? best.target + path.slice(best.prefix.length) : path;
}

/** The files reachable from the roots through imports, roots first */
export function importClosure(files: Record<string, string>, roots: string[], remappings: string[] = []): string[] {
  const seen = new Set<string>();
  const queue = roots.filter((r) => r in files);
  while (queue.length) {
    const path = queue.shift()!;
    if (seen.has(path)) continue;
    seen.add(path);
    for (const imp of importsOf(files[path]!)) {
      const resolved = resolveImport(path, imp, remappings);
      const target = resolved in files ? resolved : imp in files ? imp : undefined;
      if (target && !seen.has(target)) queue.push(target);
    }
  }
  return [...seen];
}
