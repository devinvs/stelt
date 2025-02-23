type item = Item(u32, u32)

// Create the dynamic array and start the recursive bag filling
knapsack01 : ([item], u32) -> u32
knapsack01([], _) = 0
knapsack01(items, w) =
    let db = [0; items.len(), w]
    let db = array(items.len(), w) in
    let db = fill_knapsack(db, items, items.len(), w) in
    db[n][w]
    
fill_knapsack : ([[maybe<value>]], [item], u32, u32) -> bag
fill_knapsack(bag, items, i, w) =
    if wi > w then
        // If the weight of this item is greater than
        // our target, compute the value of using the
        // previous item (we work backwards)
        bag[i-1, w]
          .or_else(_ -> fill_knapsack(bag, items, i-1, w)[i-1, w])
    else
        // Otherwise compute the value for
        //   the bag using the previous item at this weight
        //   the bag using the previous item with this item included
        // This means we subtract our weight from our budget and
        // add the value. Max value wins.
        let (lv, rv) = match (bag[i-1, w].flatten(), bag[i-1, w-wi].flatten()) with [
            (Some(lv), Some(rv)) -> (lv, rv)
            (_, _) ->
                let bag = fill_knapsack(bag, items, i-1, w) in
                let bag = fill_knapsack(bag, items, i-1, w-wi) in
                (bag[i-1, w], bag[i-1, w-wi])
        ] in max(lv, rv)
where (wi, vi) = items[i]

