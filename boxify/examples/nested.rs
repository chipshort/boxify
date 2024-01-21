struct Parent {
    pub child: Child,
}

struct Child {
    pub value: u32,
    pub grand_child: GrandChild,
}

struct GrandChild {
    pub vec: Vec<u8>,
    pub huge_array: [u8; 1024 * 1024 * 1024],
}

fn main() {
    let v = vec![1, 2, 3];
    let mut value = boxify::boxify!(Parent {
        child: Child {
            value: 42,
            grand_child: GrandChild {
                vec: v,
                huge_array: [42; 1024 * 1024 * 1024],
            },
        },
    });

    value.as_mut().child.grand_child.huge_array[100] = 21;
    println!(
        "value.child.grand_child.huge_array[100] = {}",
        value.child.grand_child.huge_array[100]
    );
}
