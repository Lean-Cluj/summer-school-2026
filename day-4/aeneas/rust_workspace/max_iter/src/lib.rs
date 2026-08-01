pub fn find_max(arr: &[i32]) -> Option<i32> {
    if arr.is_empty() {
        return None;
    }

    let mut max_val = arr[0];

    for i in 1..arr.len() {
        if arr[i] > max_val {
            max_val = arr[i];
        }
    }

    Some(max_val)
}

