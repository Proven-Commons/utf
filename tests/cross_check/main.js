// Reads one hex-encoded byte string per line and prints whether Node's
// TextDecoder, with fatal set, accepts it, with the code points it
// reads: "OK:" and lower case hex code points separated by commas, or
// "REJECT". With the argument "lossy", fatal is not set, so the decoder
// puts U+FFFD in place of bad bytes. Used by tests/cross_check.py.
const readline = require("readline");
const lossy = process.argv[2] === "lossy";
const decoder = new TextDecoder("utf-8", { fatal: !lossy, ignoreBOM: true });
const lines = [];
readline.createInterface({ input: process.stdin }).on("line", (line) => {
  try {
    const s = decoder.decode(Buffer.from(line, "hex"));
    lines.push("OK:" + Array.from(s, (c) => c.codePointAt(0).toString(16)).join(","));
  } catch (e) {
    lines.push("REJECT");
  }
}).on("close", () => process.stdout.write(lines.map((l) => l + "\n").join("")));
