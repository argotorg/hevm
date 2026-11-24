// Usage: node serve.mjs [hevm port] [page port]  -- serves the page and passes its API calls on to hevm,
// so the browser sees one origin and hevm needs no CORS
import fs from "node:fs";
import http from "node:http";
import path from "node:path";
import { fileURLToPath } from "node:url";

const hevmPort = Number(process.argv[2] ?? 7317);
const port = Number(process.argv[3] ?? 7318);
const dir = path.dirname(fileURLToPath(import.meta.url));
const files = {
  "/": ["index.html", "text/html; charset=utf-8"],
  "/debugger.js": [path.join("dist", "debugger.js"), "text/javascript; charset=utf-8"],
};
// as hevm checks, so that a site whose name points here (DNS rebinding) cannot get through
const hosts = [`127.0.0.1:${port}`, `localhost:${port}`];

http
  .createServer((req, res) => {
    if (!hosts.includes((req.headers.host ?? "").toLowerCase())) {
      res.writeHead(403, { "content-type": "text/plain" });
      res.end(`forbidden: the Host header must be one of ${hosts.join(" ")}`);
      return;
    }
    const file = req.method === "GET" ? files[req.url ?? ""] : undefined;
    if (file !== undefined) {
      fs.readFile(path.join(dir, file[0]), (err, data) => {
        if (err) {
          res.writeHead(500, { "content-type": "text/plain" });
          res.end(`cannot read ${file[0]}, run ./build.sh first: ${err.message}`);
        } else {
          res.writeHead(200, { "content-type": file[1] });
          res.end(data);
        }
      });
      return;
    }
    const upstream = http.request(
      { host: "127.0.0.1", port: hevmPort, path: req.url, method: req.method, headers: { ...req.headers, host: `127.0.0.1:${hevmPort}` } },
      (r) => {
        res.writeHead(r.statusCode ?? 502, r.headers);
        r.pipe(res);
      },
    );
    upstream.on("error", (e) => {
      res.writeHead(502, { "content-type": "text/plain" });
      res.end(`cannot reach hevm on port ${hevmPort}: ${e.message}`);
    });
    req.pipe(upstream);
  })
  .listen(port, "127.0.0.1", () => console.log(`hevm debugger page at http://127.0.0.1:${port}, for hevm on port ${hevmPort}`));
