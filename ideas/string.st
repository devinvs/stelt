// a utf8 encoded string type with three fields
// - buf : pointer to the utf8 buffer
// - off : offset to the start of our string in bytes
// - len : length of our slice in bytes
type string = String(ptr buf, usize off, usize len)

empty : string -> bool
empty(String(_, off, len)) = len == 0

pop : string -> maybe<(char, string)>
pop(String(buf, off, len)) =
	if len == 0
		then None
		else Some((buf[off], String(buf, off+1, len-1)))

split_at : (string, usize) -> maybe<(string, string)>
split_at(String(buf, off, len), at) =
	if at >= len
		then None
		else Some(String(buf, off, at), String(buf, off+at+1, len-at))

slice : (string, usize, usize) -> maybe<string>
slice(String(buf, off, len), from, to) =
	if from >= len or to >= len
		then None
		else Some(String(buf, off+from, to-from))

print : string -> ()
print(String(buf, off, len)) = write(1, buf+off, len)
