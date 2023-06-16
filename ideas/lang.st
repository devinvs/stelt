use webserver

type register((Server, string, Request->Response) -> ())

type handler(Request -> Response)

handler(JSON(data)) = "success"
handler(_) = "error: JSON required"

type main(() -> ())
main = {
    let s = new_server()
    register(s, "/get", handler)
    run(s)
}


type Shape(
    type Circle(
        center (u8, u8),
        radius u8
    ) | type Square(
        corner (u8, u8),
        size u8,
    )
)

type area(Shape->u8)

def pi 3.14
area(Circle(_, r)) = r*r*pi
area(Square(_, s)) = s*s


