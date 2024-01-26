use core::mem::size_of;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn unaligned_write<T: Copy, const SIZE: usize>(array: &mut [T; SIZE], value: T) {
    let array = array.as_mut_ptr();
    if size_of::<T>() == 1 {
        // in this case, we can use `ptr::write_bytes` instead of `ptr::write`
        // SAFETY: we just checked that T is 1 byte, so casting to *const u8 is valid
        let value_byte: *const u8 = core::ptr::addr_of!(value) as *const u8;
        // also casting array to *mut u8 for alignment reasons (basically what an unaligned write does)
        unsafe { core::ptr::write_bytes(array as *mut u8, *value_byte, SIZE) };
    } else {
        for i in 0..SIZE {
            // write the value to the array
            unsafe { array.add(i).write_unaligned(value) };
        }
    }
}

fn aligned_write<T: Copy, const SIZE: usize>(array: &mut [T; SIZE], value: T) {
    let array = array.as_mut_ptr();
    if size_of::<T>() == 1 {
        // in this case, we can use `ptr::write_bytes` instead of `ptr::write`
        // SAFETY: we just checked that T is 1 byte, so casting to *const u8 is valid
        let value_byte: *const u8 = core::ptr::addr_of!(value) as *const u8;
        unsafe { core::ptr::write_bytes(array, *value_byte, SIZE) };
    } else {
        for i in 0..SIZE {
            // write the value to the array
            unsafe { array.add(i).write(value) };
        }
    }
}

fn multibyte_writes(c: &mut Criterion) {
    const SIZE: usize = 5000000;
    let mut array = [0u128; SIZE / 16];
    c.bench_function("unaligned multibyte write", |b| {
        b.iter(|| unaligned_write(&mut array, black_box(42u128)))
    });
    c.bench_function("aligned multibyte write", |b| {
        b.iter(|| aligned_write(&mut array, black_box(42u128)))
    });
}

fn singlebyte_writes(c: &mut Criterion) {
    const SIZE: usize = 5000000;
    let mut array = [0u8; SIZE];
    c.bench_function("unaligned single byte write", |b| {
        b.iter(|| unaligned_write(&mut array, black_box(42u8)))
    });
    c.bench_function("aligned single byte write", |b| {
        b.iter(|| aligned_write(&mut array, black_box(42u8)))
    });
}

criterion_group!(benches, multibyte_writes, singlebyte_writes);
criterion_main!(benches);
