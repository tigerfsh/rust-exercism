use time::PrimitiveDateTime as DateTime;
use time::{Date, Duration, Month, Time};
use time_macros::datetime;

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
