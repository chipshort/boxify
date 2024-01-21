#[cfg(not(miri))]
const SIZE: usize = 1024 * 1024;
#[cfg(miri)]
const SIZE: usize = 1024;

struct Example<T> {
    pub huge_array: [T; SIZE],
}

fn main() {
    // this would overflow the stack:
    // let mut e = Box::new(Example {
    //     huge_array: [42; SIZE],
    // });

    // this does not:
    let mut e = boxify::boxify!(Example {
        huge_array: [42; SIZE],
    });

    e.as_mut().huge_array[0] = 43;
    println!("e.huge_array[0] = {}", e.huge_array[0]);
}
