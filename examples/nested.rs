struct Parent {
    pub child: Child,
}

struct Child {
    pub value: u32,
    pub grand_child: GrandChild,
}

struct GrandChild {
    pub huge_array: [u8; 1024 * 1024 * 1024],
}

fn main() {
    let mut value = boxify::boxify!(Parent {
        child: Child {
            value: 42,
            grand_child: GrandChild {
                huge_array: [42; 1024 * 1024 * 1024],
            },
        },
    });

    value.as_mut().child.value = 21;
    println!("value.child.value = {}", value.child.value);
}
