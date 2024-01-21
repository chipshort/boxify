struct Parent(Child);

struct Child {
    pub value: u32,
    pub grand_child: GrandChild,
}

#[cfg(not(miri))]
const SIZE: usize = 1024 * 1024 * 1024;
#[cfg(miri)]
const SIZE: usize = 1024;

struct GrandChild {
    pub vec: Vec<u8>,
    pub huge_array: [u8; SIZE],
}

fn main() {
    let v = vec![1, 2, 3];
    let mut value = boxify::boxify!(Parent(Child {
        value: 42,
        grand_child: GrandChild {
            vec: v,
            huge_array: [42; SIZE],
        },
    }));

    value.as_mut().0.grand_child.huge_array[100] = 21;
    println!(
        "sum(value.0.grand_child.huge_array) = {}",
        value
            .0
            .grand_child
            .huge_array
            .iter()
            .map(|i| *i as u128)
            .sum::<u128>()
    );
}
