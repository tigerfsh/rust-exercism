use time::PrimitiveDateTime as DateTime;
use time::Duration;

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
        Self { hours: h, minutes: m, seconds: 0 }
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

    use time_macros::datetime;
    use time::{Date, Time, Month};

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
