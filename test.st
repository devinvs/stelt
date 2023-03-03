type Shape (
    type Square (
        corner (u8, u8),
        u8,
        height u8
    )
    | type Circle (
        center (u8, u8),
        radius u8
    )
)
