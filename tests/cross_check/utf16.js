// UTF-16 in Node, for tests/cross_check.py. Reads one hex string per
// line and prints an answer in the tool's form: "OK:" and lower case
// hex code points separated by commas, or "REJECT", or units in hex.
// The argument picks the operation:
//   units       the line is UTF-16 code units, four hex digits each;
//               OK and the code points if isWellFormed(), else REJECT
//   units-lossy the code points of toWellFormed()
//   wf          the units of toWellFormed()
//   be, le      TextDecoder("utf-16be" / "utf-16le") with fatal and
//               ignoreBOM set, on the line as bytes
//   be-lossy, le-lossy   the same, without fatal
const readline = require("readline");
const mode = process.argv[2];
const points = (s) => "OK:" + Array.from(s, (c) => c.codePointAt(0).toString(16)).join(",");
const unitsOf = (line) => {
  const us = [];
  for (let i = 0; i + 4 <= line.length; i += 4) us.push(parseInt(line.slice(i, i + 4), 16));
  return String.fromCharCode(...us);
};
const hexUnits = (s) => Array.from({ length: s.length }, (_, i) =>
  s.charCodeAt(i).toString(16).padStart(4, "0")).join("");
const decoders = {
  be: new TextDecoder("utf-16be", { fatal: true, ignoreBOM: true }),
  le: new TextDecoder("utf-16le", { fatal: true, ignoreBOM: true }),
  "be-lossy": new TextDecoder("utf-16be", { ignoreBOM: true }),
  "le-lossy": new TextDecoder("utf-16le", { ignoreBOM: true }),
};
const answer = (line) => {
  if (mode === "units") {
    const s = unitsOf(line);
    return s.isWellFormed() ? points(s) : "REJECT";
  }
  if (mode === "units-lossy") return points(unitsOf(line).toWellFormed());
  if (mode === "wf") return hexUnits(unitsOf(line).toWellFormed());
  try {
    return points(decoders[mode].decode(Buffer.from(line, "hex")));
  } catch (e) {
    return "REJECT";
  }
};
const lines = [];
readline.createInterface({ input: process.stdin }).on("line", (line) => lines.push(answer(line)))
  .on("close", () => process.stdout.write(lines.map((l) => l + "\n").join("")));
