pub fn find_pair(xs: &[u32], target: u32) -> u32 {
    let mut found = 0;
    let mut i = 0;
    'outer: while i < xs.len() {
        let mut j = i + 1;
        loop {
            if j >= xs.len() {
                break;
            }
            if xs[i] + xs[j] == target {
                found = 1;
                break 'outer;
            }
            j += 1;
        }
        i += 1;
    }
    found
}

pub fn count_rows(rows: Vec<Vec<u32>>) -> u32 {
    let mut c = 0;
    let mut rows = rows;
    'rows: while let Some(row) = rows.pop() {
        'cells: loop {
            for x in &row {
                if *x == 0 {
                    continue 'rows;
                }
                if *x > 100 {
                    break 'cells;
                }
            }
            c += 1;
            break;
        }
    }
    c
}

pub fn stop_in_condition(n: u32) -> u32 {
    let mut i = 0;
    'w: while {
        if i > 10 {
            break 'w;
        }
        i < n
    } {
        i += 1;
    }
    i
}
