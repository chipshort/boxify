struct Example<T> {
    pub huge_array: [T; 1024 * 1024],
}

fn main() {
    // this would overflow the stack:
    // let mut e = Box::new(Example {
    //     huge_array: [42; 1024 * 1024],
    // });

    // this does not:
    let mut e = boxify::boxify!(Example {
        huge_array: [42; 1024 * 1024],
    });

    e.as_mut().huge_array[0] = 43;
    println!("e.huge_array[0] = {}", e.huge_array[0]);
}
