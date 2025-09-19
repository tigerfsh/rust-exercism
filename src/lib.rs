
use time::Duration;
use time::PrimitiveDateTime as DateTime;

pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// Returns a DateTime one billion seconds after start.
pub fn after(start: DateTime) -> DateTime {
    start + Duration::seconds(1_000_000_000)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Clock {
    hours: i32,
    minutes: i32,
    seconds: i32,
}

use std::fmt;

impl fmt::Display for Clock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:02}:{:02}", self.hours, self.minutes)
    }
}

impl Clock {
    pub fn new(hours: i32, minutes: i32) -> Self {
        let extra_h = minutes / 60;
        let mut m = minutes % 60;
        let mut h = (hours + extra_h) % 24;

        if m < 0 {
            h -= 1;
            m += 60;
        }

        h = ((h % 24) + 24) % 24;
        m = ((m % 60) + 60) % 60;
        Self {
            hours: h,
            minutes: m,
            seconds: 0,
        }
    }

    pub fn add_minutes(&self, minutes: i32) -> Self {
        let mut total_minutes = self.hours * 60 + self.minutes + minutes;
        if total_minutes < 0 {
            total_minutes = total_minutes % (24 * 60) + 24 * 60
        }

        let h = ((total_minutes / 60) % 24 + 24) % 24;
        let m = ((total_minutes % 60) + 60) % 60;
        Self {
            hours: h,
            minutes: m,
            seconds: self.seconds,
        }
    }
}

use std::collections::HashSet;

pub fn anagrams_for<'a>(word: &str, possible_anagrams: &[&'a str]) -> HashSet<&'a str> {
    // Helper: normalize a word (lowercase, sort chars)
    fn normalize(s: &str) -> Vec<char> {
        let mut chars: Vec<char> = s.chars().flat_map(|c| c.to_lowercase()).collect();
        chars.sort_unstable();
        chars
    }

    let word_norm = normalize(word);
    let word_lower = word.to_lowercase();

    possible_anagrams
        .iter()
        .filter_map(|&candidate| {
            if candidate.to_lowercase() == word_lower {
                return None;
            }
            if normalize(candidate) == word_norm {
                Some(candidate)
            } else {
                None
            }
        })
        .collect()
}

#[derive(Debug)]
pub struct CDuration {
    seconds: u64,
}

impl From<u64> for CDuration {
    fn from(s: u64) -> Self {
        CDuration { seconds: s }
    }
}

pub trait Planet {
    // Orbital period in Earth years
    const ORBITAL_PERIOD: f64;

    fn years_during(d: &CDuration) -> f64 {
        let earth_year_seconds = 31_557_600.0;
        let seconds = d.seconds as f64;
        seconds / (Self::ORBITAL_PERIOD * earth_year_seconds)
    }
}

pub struct Mercury;
pub struct Venus;
pub struct Earth;
pub struct Mars;
pub struct Jupiter;
pub struct Saturn;
pub struct Uranus;
pub struct Neptune;

impl Planet for Mercury {
    const ORBITAL_PERIOD: f64 = 0.2408467;
}
impl Planet for Venus {
    const ORBITAL_PERIOD: f64 = 0.61519726;
}
impl Planet for Earth {
    const ORBITAL_PERIOD: f64 = 1.0;
}
impl Planet for Mars {
    const ORBITAL_PERIOD: f64 = 1.8808158;
}
impl Planet for Jupiter {
    const ORBITAL_PERIOD: f64 = 11.862615;
}
impl Planet for Saturn {
    const ORBITAL_PERIOD: f64 = 29.447498;
}
impl Planet for Uranus {
    const ORBITAL_PERIOD: f64 = 84.016846;
}
impl Planet for Neptune {
    const ORBITAL_PERIOD: f64 = 164.79132;
}

#[cfg(test)]
mod planet_tests {
    use super::*;

    #[test]
    fn test_earth_years() {
        let duration = CDuration::from(31_557_600);
        let years = Earth::years_during(&duration);
        assert!((years - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_mercury_years() {
        let duration = CDuration::from(31_557_600);
        let years = Mercury::years_during(&duration);
        assert!((years - (1.0 / 0.2408467)).abs() < 1e-6);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Comparison {
    Equal,
    Sublist,
    Superlist,
    Unequal,
}

pub fn sublist(first_list: &[i32], second_list: &[i32]) -> Comparison {
    fn is_sublist(small: &[i32], big: &[i32]) -> bool {
        if small.is_empty() {
            return true;
        }
        if small.len() > big.len() {
            return false;
        }
        big.windows(small.len()).any(|window| window == small)
    }

    if first_list == second_list {
        Comparison::Equal
    } else if is_sublist(first_list, second_list) {
        Comparison::Sublist
    } else if is_sublist(second_list, first_list) {
        Comparison::Superlist
    } else {
        Comparison::Unequal
    }
}

/*
Introduction
Flower Field is a compassionate reimagining of the popular game Minesweeper. The object of the game is to find all the flowers in the garden using numeric hints that indicate how many flowers are directly adjacent (horizontally, vertically, diagonally) to a square. "Flower Field" shipped in regional versions of Microsoft Windows in Italy, Germany, South Korea, Japan and Taiwan.

Instructions
Your task is to add flower counts to empty squares in a completed Flower Field garden. The garden itself is a rectangle board composed of squares that are either empty (' ') or a flower ('*').

For each empty square, count the number of flowers adjacent to it (horizontally, vertically, diagonally). If the empty square has no adjacent flowers, leave it empty. Otherwise replace it with the count of adjacent flowers.

For example, you may receive a 5 x 4 board like this (empty spaces are represented here with the '·' character for display on screen):

·*·*·
··*··
··*··
·····
Which your code should transform into this:

1*3*1
13*31
·2*2·
·111·
Performance Hint
All the inputs and outputs are in ASCII. Rust Strings and &str are utf8, so while one might expect "Hello".chars() to be simple, it actually has to check each char to see if it's 1, 2, 3 or 4 u8s long. If we know a &str is ASCII then we can call .as_bytes() and refer to the underlying data as a &[u8] (byte slice). Iterating over a slice of ASCII bytes is much quicker as there are no codepoints involved - every ASCII byte is one u8 long.

Can you complete the challenge without cloning the input?

*/

/*
let b = "abc";
let c = b.as_bytes();
println!("c: {c:?}"); // c: [97, 98, 99]
*/

pub fn annotate(garden: &[&str]) -> Vec<String> {
    let star_char_but_byte = 42u8;

    let height = garden.len();
    if height == 0 {
        return Vec::new();
    }
    let width = garden[0].len();
    let mut result = Vec::with_capacity(height);

    for (i, row) in garden.iter().enumerate() {
        let bytes = row.as_bytes();
        let mut annotated_row = Vec::with_capacity(width);
        for (j, &cell) in bytes.iter().enumerate() {
            if cell == star_char_but_byte {
                annotated_row.push(star_char_but_byte);
            } else {
                let mut count = 0;
                for di in [-1i32, 0, 1] {
                    for dj in [-1i32, 0, 1] {
                        if di == 0 && dj == 0 {
                            continue;
                        }
                        let ni = i as i32 + di;
                        let nj = j as i32 + dj;
                        if ni >= 0
                            && ni < height as i32
                            && nj >= 0
                            && nj < width as i32
                            && garden[ni as usize].as_bytes()[nj as usize] == star_char_but_byte
                        {
                            count += 1;
                        }
                    }
                }
                if count == 0 {
                    annotated_row.push(b' ');
                } else {
                    annotated_row.push(b'0' + count as u8);
                }
            }
        }
        // Safety: all bytes are ASCII, so this is safe
        result.push(String::from_utf8(annotated_row).unwrap());
    }
    result
}

pub fn is_valid(code: &str) -> bool {
    fn double_one_num(n: u32) -> u32 {
        let dn = n * 2;
        if dn > 9 {
            let a = dn / 10;
            let b = dn % 10;
            return a + b;
        }

        dn
    }

    let mut result = Vec::new();

    let code_no_spaces: String = code.chars().filter(|c| !c.is_whitespace()).collect();
    let code = &code_no_spaces;
    for (reverse_index, char) in code.chars().rev().enumerate() {
        // let num = char.to_digit(10);
        let Some(num) = char.to_digit(10) else {
            return false;
        };

        let position_from_end = reverse_index + 1;
        if position_from_end % 2 == 0 {
            result.push(double_one_num(num));
        } else {
            result.push(num);
        }
    }

    let total_num: u32 = result.iter().sum();

    if result.len() == 1 && total_num == 0 {
        return false;
    }

    if result.len() > 1 && total_num == 0 {
        return true;
    }

    total_num % 10 == 0
}

pub fn is_armstrong_number(num: u32) -> bool {
    let num_string = num.to_string();

    let total = num_string
        .chars()
        .filter_map(|n| n.to_digit(10))
        .map(|num| num.pow(num_string.len() as u32))
        .sum::<u32>();

    num == total
}

pub fn square_of_sum(n: u32) -> u32 {
    (1..=n).sum::<u32>().pow(2)
}

pub fn sum_of_squares(n: u32) -> u32 {
    (1..=n).map(|n| n.pow(2)).sum::<u32>()
}

pub fn difference(n: u32) -> u32 {
    square_of_sum(n) - sum_of_squares(n)
}

// 判断是否符合要求
// 题目要求：
// 1. 计算第 n 个格子的麦粒数（第 1 格为 1 粒，每一格是前一格的 2 倍）
// 2. 计算整个棋盘（64 格）上的麦粒总数

// 第 n 格的麦粒数是 2^(n-1)
pub fn square(s: u32) -> u64 {
    if s == 0 || s > 64 {
        panic!("Square must be between 1 and 64");
    }
    1u64 << (s - 1)
}

// 总数是 2^64 - 1
pub fn total() -> u64 {
    (1..=64).map(square).sum::<u64>()
}

pub fn is_leap_year(year: u64) -> bool {
    if year % 4 == 0 {
        if year % 100 == 0 {
            if year % 400 == 0 {
                return true;
            }
            return false;
        }
        return true;
    }

    false
}

/*
Given a number n, determine what the nth prime is.

By listing the first six prime numbers: 2, 3, 5, 7, 11, and 13, we can see that the 6th prime is 13.

If your language provides methods in the standard library to deal with prime numbers, pretend they don't exist and implement them yourself.

Remember that while people commonly count with 1-based indexing (i.e. "the 6th prime is 13"), many programming languages, including Rust, use 0-based indexing (i.e. primes[5] == 13). Use 0-based indexing for your implementation.
*/

pub fn nth(n: u32) -> u32 {
    if n == 0 {
        return 2;
    }
    let mut count = 1; // 2 is the first prime (index 0)
    let mut candidate = 3;
    while count <= n {
        let mut is_prime = true;
        let sqrt = (candidate as f64).sqrt() as u32;
        for i in 2..=sqrt {
            if candidate % i == 0 {
                is_prime = false;
                break;
            }
        }
        if is_prime {
            if count == n {
                return candidate;
            }
            count += 1;
        }
        candidate += 2; // skip even numbers
    }
    unreachable!()
}

/*
Instructions
Compute the prime factors of a given natural number.

A prime number is only evenly divisible by itself and 1.

Note that 1 is not a prime number.

Example
What are the prime factors of 60?

Our first divisor is 2. 2 goes into 60, leaving 30.
2 goes into 30, leaving 15.
2 doesn't go cleanly into 15. So let's move on to our next divisor, 3.
3 goes cleanly into 15, leaving 5.
3 does not go cleanly into 5. The next possible factor is 4.
4 does not go cleanly into 5. The next possible factor is 5.
5 does go cleanly into 5.
We're left only with 1, so now, we're done.
Our successful divisors in that computation represent the list of prime factors of 60: 2, 2, 3, and 5.
*/

pub fn factors(mut n: u64) -> Vec<u64> {
    let mut result = Vec::new();
    if n < 2 {
        return result;
    }
    let mut divisor = 2;
    while n > 1 {
        while n % divisor == 0 {
            result.push(divisor);
            n /= divisor;
        }
        divisor += 1;
        // 优化：如果divisor*divisor > n，且n>1，则n本身是质数
        if divisor * divisor > n && n > 1 {
            result.push(n);
            break;
        }
    }
    result
}

pub fn abbreviate(phrase: &str) -> String {
    let mut acronym = String::new();
    let mut prev_is_separator = true;
    let mut pre_is_lower_case = false;

    fn is_super_ascii_alphabetic(c: char) -> bool {
        if c.is_ascii_alphabetic() || c == '\'' {
            return true;
        }
        false
    }

    let nor_phrase = phrase.replace("and", " ");
    for c in nor_phrase.chars() {
        if is_super_ascii_alphabetic(c) {
            if prev_is_separator {
                acronym.push(c.to_ascii_uppercase());
            } else {
                if pre_is_lower_case && c.is_ascii_uppercase() {
                    acronym.push(c.to_ascii_uppercase());
                }
            }
            prev_is_separator = false;
        } else {
            if c == '-' || c.is_whitespace() || !is_super_ascii_alphabetic(c) {
                prev_is_separator = true;
            }
        }

        pre_is_lower_case = c.is_ascii_lowercase();
    }

    acronym
}

#[cfg(test)]
mod abbreviate_tests {
    use super::*;

    #[test]
    fn test_basic() {
        assert_eq!(abbreviate("As Soon As Possible"), "ASAP");
    }

    #[test]
    fn test_hyphenated() {
        assert_eq!(abbreviate("Liquid-crystal display"), "LCD");
    }

    #[test]
    fn test_punctuation() {
        assert_eq!(abbreviate("Thank George It's Friday!"), "TGIF");
    }

    #[test]
    fn test_single_word() {
        assert_eq!(abbreviate("Rust"), "R");
    }

    #[test]
    fn test_empty_string() {
        assert_eq!(abbreviate(""), "");
    }

    #[test]
    fn test_multiple_hyphens_and_spaces() {
        assert_eq!(abbreviate("Hyper-text Markup Language"), "HTML");
    }

    #[test]
    fn test_leading_and_trailing_whitespace() {
        assert_eq!(
            abbreviate("  National Aeronautics and Space Administration  "),
            "NASA"
        );
    }

    #[test]
    fn test_all_lowercase() {
        assert_eq!(abbreviate("central processing unit"), "CPU");
    }

    #[test]
    fn test_mixed_case_and_punctuation() {
        assert_eq!(
            abbreviate("Complementary metal-oxide semiconductor!"),
            "CMOS"
        );
    }

    #[test]
    fn test_upper_char_in_word() {
        assert_eq!(abbreviate("HyperText Markup Language"), "HTML")
    }
}

#[cfg(test)]
mod factors_tests {
    use super::*;

    #[test]
    fn test_factors_of_1() {
        assert_eq!(factors(1), vec![]);
    }

    #[test]
    fn test_factors_of_2() {
        assert_eq!(factors(2), vec![2]);
    }

    #[test]
    fn test_factors_of_3() {
        assert_eq!(factors(3), vec![3]);
    }

    #[test]
    fn test_factors_of_4() {
        assert_eq!(factors(4), vec![2, 2]);
    }

    #[test]
    fn test_factors_of_6() {
        assert_eq!(factors(6), vec![2, 3]);
    }

    #[test]
    fn test_factors_of_60() {
        assert_eq!(factors(60), vec![2, 2, 3, 5]);
    }

    #[test]
    fn test_factors_of_large_prime() {
        assert_eq!(factors(97), vec![97]);
    }

    #[test]
    fn test_factors_of_large_composite() {
        assert_eq!(
            factors(2 * 2 * 3 * 3 * 5 * 7 * 11),
            vec![2, 2, 3, 3, 5, 7, 11]
        );
    }
}

#[cfg(test)]
mod nth_prime_tests {
    use super::*;

    #[test]
    fn test_first_prime() {
        assert_eq!(nth(0), 2);
    }

    #[test]
    fn test_second_prime() {
        assert_eq!(nth(1), 3);
    }

    #[test]
    fn test_sixth_prime() {
        assert_eq!(nth(5), 13);
    }

    #[test]
    fn test_tenth_prime() {
        assert_eq!(nth(9), 29);
    }

    #[test]
    fn test_large_prime() {
        assert_eq!(nth(100), 547);
    }
}

#[cfg(test)]
mod armstrong_tests {
    use super::*;

    #[test]
    fn test_single_digit() {
        assert!(is_armstrong_number(5));
        assert!(is_armstrong_number(0));
        assert!(is_armstrong_number(9));
    }

    #[test]
    fn test_two_digits() {
        assert!(!is_armstrong_number(10));
        assert!(!is_armstrong_number(99));
    }

    #[test]
    fn test_three_digits() {
        assert!(is_armstrong_number(153));
        assert!(is_armstrong_number(370));
        assert!(is_armstrong_number(371));
        assert!(is_armstrong_number(407));
        assert!(!is_armstrong_number(100));
        assert!(!is_armstrong_number(200));
    }

    #[test]
    fn test_four_digits() {
        assert!(is_armstrong_number(1634));
        assert!(!is_armstrong_number(1234));
    }

    #[test]
    fn test_large_number() {
        assert!(is_armstrong_number(9474));
        assert!(!is_armstrong_number(9475));
    }
}

#[cfg(test)]
mod luhn_tests {
    use super::*;

    #[test]
    fn test_is_valid() {
        assert!(is_valid("4539 3195 0343 6467"));
        assert!(!is_valid("0"));
        assert!(!is_valid(" 0"));
        assert!(!is_valid("123#4"));
        assert!(is_valid("0000 0"));
    }
}

#[cfg(test)]
mod sublist_tests {
    use super::*;

    #[test]
    fn test_equal_lists() {
        let a = [1, 2, 3];
        let b = [1, 2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Equal);
    }

    #[test]
    fn test_sublist_at_start() {
        let a = [1, 2];
        let b = [1, 2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Sublist);
    }

    #[test]
    fn test_sublist_at_end() {
        let a = [2, 3];
        let b = [1, 2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Sublist);
    }

    #[test]
    fn test_superlist() {
        let a = [1, 2, 3, 4];
        let b = [2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Superlist);
    }

    #[test]
    fn test_unequal_lists() {
        let a = [1, 2, 4];
        let b = [1, 2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Unequal);
    }

    #[test]
    fn test_empty_and_nonempty() {
        let a: [i32; 0] = [];
        let b = [1, 2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Sublist);
        assert_eq!(sublist(&b, &a), Comparison::Superlist);
    }

    #[test]
    fn test_both_empty() {
        let a: [i32; 0] = [];
        let b: [i32; 0] = [];
        assert_eq!(sublist(&a, &b), Comparison::Equal);
    }

    #[test]
    fn test_single_element_sublist() {
        let a = [2];
        let b = [1, 2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Sublist);
    }

    #[test]
    fn test_no_overlap() {
        let a = [4, 5, 6];
        let b = [1, 2, 3];
        assert_eq!(sublist(&a, &b), Comparison::Unequal);
    }

    #[test]
    fn test_repeated_elements() {
        let a = [1, 1, 2];
        let b = [1, 1, 1, 2, 1];
        assert_eq!(sublist(&a, &b), Comparison::Sublist);
    }
}

#[cfg(test)]
mod anagram_tests {
    use super::anagrams_for;
    use std::collections::HashSet;

    fn set_of<'a>(items: &[&'a str]) -> HashSet<&'a str> {
        items.iter().copied().collect()
    }

    #[test]
    fn test_no_anagrams() {
        let word = "hello";
        let candidates = ["world", "rust", "test"];
        let result = anagrams_for(word, &candidates);
        assert!(result.is_empty());
    }

    #[test]
    fn test_simple_anagram() {
        let word = "listen";
        let candidates = ["enlists", "google", "inlets", "banana"];
        let result = anagrams_for(word, &candidates);
        assert_eq!(result, set_of(&["inlets"]));
    }

    #[test]
    fn test_multiple_anagrams() {
        let word = "master";
        let candidates = ["stream", "maters", "tamers", "something"];
        let result = anagrams_for(word, &candidates);
        assert_eq!(result, set_of(&["stream", "maters", "tamers"]));
    }

    #[test]
    fn test_case_insensitive() {
        let word = "Orchestra";
        let candidates = ["cashregister", "Carthorse", "radishes"];
        let result = anagrams_for(word, &candidates);
        assert_eq!(result, set_of(&["Carthorse"]));
    }

    #[test]
    fn test_same_word_not_anagram() {
        let word = "banana";
        let candidates = ["Banana"];
        let result = anagrams_for(word, &candidates);
        assert!(result.is_empty());
    }

    #[test]
    fn test_unicode_anagram() {
        let word = "åbc";
        let candidates = ["båc", "cab", "abc"];
        let result = anagrams_for(word, &candidates);
        assert_eq!(result, set_of(&["båc"]));
    }
}

#[cfg(test)]
mod clock_tests {
    use super::Clock;

    #[test]
    fn test_new_basic() {
        let c = Clock::new(10, 30);
        assert_eq!(c.hours, 10);
        assert_eq!(c.minutes, 30);
        assert_eq!(c.seconds, 0);
    }

    #[test]
    fn test_new_to_string() {
        assert_eq!(Clock::new(8, 0).to_string(), "08:00");
    }
    #[test]
    fn test_new_eq() {
        let c1 = Clock::new(12, 30);
        let c2 = Clock::new(12, 30);
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_new_overflow_hours() {
        let c = Clock::new(25, 0);
        assert_eq!(c.hours, 1);
        assert_eq!(c.minutes, 0);
    }

    #[test]
    fn test_new_overflow_minutes() {
        let c = Clock::new(6, 65);
        assert_eq!(c.hours, 7);
        assert_eq!(c.minutes, 5);
    }

    #[test]
    fn test_new_negative_minutes() {
        let c = Clock::new(10, -15);
        assert_eq!(c.hours, 9);
        assert_eq!(c.minutes, 45);
    }

    #[test]
    fn test_new_negative_hours() {
        let c = Clock::new(-1, 0);
        assert_eq!(c.hours, 23);
        assert_eq!(c.minutes, 0);
    }

    #[test]
    fn test_new_large_negative_minutes() {
        let c = Clock::new(0, -160);
        assert_eq!(c.hours, 21);
        assert_eq!(c.minutes, 20);
    }

    #[test]
    fn test_add_minutes_basic() {
        let c = Clock::new(10, 30);
        let c2 = c.add_minutes(15);
        assert_eq!(c2.hours, 10);
        assert_eq!(c2.minutes, 45);
    }

    #[test]
    fn test_add_minutes_overflow_hour() {
        let c = Clock::new(23, 50);
        let c2 = c.add_minutes(15);
        assert_eq!(c2.hours, 0);
        assert_eq!(c2.minutes, 5);
    }

    #[test]
    fn test_add_minutes_negative() {
        let c = Clock::new(0, 10);
        let c2 = c.add_minutes(-20);
        assert_eq!(c2.hours, 23);
        assert_eq!(c2.minutes, 50);
    }

    #[test]
    fn test_add_minutes_large_negative() {
        let c = Clock::new(5, 0);
        let c2 = c.add_minutes(-300);
        assert_eq!(c2.hours, 0);
        assert_eq!(c2.minutes, 0);
    }

    #[test]
    fn test_add_minutes_multiple_days() {
        let c = Clock::new(1, 0);
        let c2 = c.add_minutes(1440 * 2 + 30); // 2 days and 30 minutes
        assert_eq!(c2.hours, 1);
        assert_eq!(c2.minutes, 30);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use time::{Date, Month, Time};
    use time_macros::datetime;

    #[test]
    fn test_after() {
        let start = datetime!(2015-01-01 0:00:00);
        let result = after(start);
        let expected = start + Duration::seconds(1_000_000_000);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_after_v2() {
        let date_today = Date::from_calendar_date(2025, Month::September, 17).unwrap();
        let time_now = Time::from_hms(15, 0, 0).unwrap();
        let start = DateTime::new(date_today, time_now);
        let result = after(start);
        let expected = start + Duration::seconds(1_000_000_000);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_add() {
        assert_eq!(add(1, 2), 3);
    }
}
