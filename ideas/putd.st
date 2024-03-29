extern type putchar: i32 -> ()
extern type puts: str -> ()

type digits: u32 -> [char]
digits(0) = []
digits(x) = if x < 10 then x else (x%10) :: digits(x/10)

type putd: i32 -> ()
putd(x) = putchar(x+48)

type putnum: i32 -> ()
putnum(0) = putd(0)
putnum(x) = putnum_h(x)

type putnum_h: i32 -> ()
putnum_h(0) = ()
putnum_h(n) = {
    putnum_h(n / 10)
    putd(n % 10)
}

