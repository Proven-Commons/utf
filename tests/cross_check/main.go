// Reads one hex-encoded byte string per line and prints whether Go's
// unicode/utf8.Valid accepts it, with the code points it reads: "OK:"
// and lower case hex code points separated by commas, or "REJECT".
// Used by tests/cross_check.py.
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"os"
	"strings"
	"unicode/utf8"
)

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		b, err := hex.DecodeString(in.Text())
		if err != nil || !utf8.Valid(b) {
			fmt.Fprintln(out, "REJECT")
			continue
		}
		parts := []string{}
		for _, r := range string(b) {
			parts = append(parts, fmt.Sprintf("%x", r))
		}
		fmt.Fprintln(out, "OK:"+strings.Join(parts, ","))
	}
}
