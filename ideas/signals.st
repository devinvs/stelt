// this is just a channel
create_signal : a -> (() -> io<a>, a -> io<()>)
create_signal =
	let c = new_channel() in
	(() -> read(c), x -> write(c, x))

