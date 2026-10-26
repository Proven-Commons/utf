// UTF-16 in Go, for tests/cross_check.py. Reads one line per input of
// UTF-16 code units, four hex digits each, and prints "OK:" and the code
// points of unicode/utf16.Decode, which gives U+FFFD for each unpaired
// surrogate, in lower case hex separated by commas.
package main

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
	"strings"
	"unicode/utf16"
)

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<26)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		line := in.Text()
		units := make([]uint16, 0, len(line)/4)
		for i := 0; i+4 <= len(line); i += 4 {
			v, _ := strconv.ParseUint(line[i:i+4], 16, 16)
			units = append(units, uint16(v))
		}
		parts := []string{}
		for _, r := range utf16.Decode(units) {
			parts = append(parts, strconv.FormatInt(int64(r), 16))
		}
		fmt.Fprintf(out, "OK:%s\n", strings.Join(parts, ","))
	}
}
