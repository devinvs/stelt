from std.cmp import eq

type char = Char(u32)
alias string = [char]

impl eq(char)
eq(Char(x), Char(y)) = x==y
