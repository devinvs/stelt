type spawn<a, b>: (a->b, a) -> handle<b>	// a handle is basically a future or smthn
type join<a>: handle<a> -> a

// run functions in parallel
type parallel<a, b>: [(a->b, a)] -> [b]
parallel(jobs) = jobs=>spawn()=>join()

