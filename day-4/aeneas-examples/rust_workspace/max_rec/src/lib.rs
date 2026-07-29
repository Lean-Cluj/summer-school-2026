pub fn find_max(arr: &[i32]) -> Option<i32> {
    if arr.is_empty() {
        None
    } else {
        Some(find_max_rec(arr, 1, arr[0]))
    }
}

// The recursive helper completely bypasses Aeneas's loop machinery
fn find_max_rec(arr: &[i32], i: usize, current_max: i32) -> i32 {
    if i >= arr.len() {
        current_max
    } else {
        let next_max = if arr[i] > current_max { arr[i] } else { current_max };
        find_max_rec(arr, i + 1, next_max)
    }
}
