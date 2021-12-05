use anyhow::{anyhow, Context, Result};
use std::fs::File;
use std::{
    collections::HashMap,
    hash::Hash,
    io::{BufRead, BufReader, Lines},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Point {
    x: i32,
    y: i32,
}

#[derive(Debug, Clone)]
struct Sweep {
    p0: Point,
    p1: Point,
}

struct Bresenham {
    dx: i32,
    dy: i32,
    sx: i32,
    sy: i32,
    err: i32,
    x0: i32,
    y0: i32,
    x1: i32,
    y1: i32,
    active: bool,
}

impl Iterator for Bresenham {
    type Item = Point;
    fn next(&mut self) -> Option<Self::Item> {
        if !self.active {
            return None;
        }

        let current = Point {
            x: self.x0,
            y: self.y0,
        };

        if self.x0 == self.x1 && self.y0 == self.y1 {
            self.active = false;
        }

        let e2 = 2 * self.err;

        if e2 > self.dy {
            self.err += self.dy;
            self.x0 += self.sx;
        }

        if e2 < self.dx {
            self.err += self.dx;
            self.y0 += self.sy;
        }

        return Some(current);
    }
}

impl Sweep {
    fn try_from(line: &String) -> Result<Self> {
        let mut coords = line
            .split(",")
            .map(|v| v.parse::<i32>())
            .filter_map(|r| r.ok());

        let p0 = Point {
            x: coords.next().ok_or(anyhow!("x0 missing"))?,
            y: coords.next().ok_or(anyhow!("y0 missing"))?,
        };
        let p1 = Point {
            x: coords.next().ok_or(anyhow!("x1 missing"))?,
            y: coords.next().ok_or(anyhow!("y1 missing"))?,
        };

        Ok(Sweep { p0, p1 })
    }

    fn is_diagonal(&self) -> bool {
        self.p0.x != self.p1.x && self.p0.y != self.p1.y
    }

    fn points(&self) -> Bresenham {
        let dx = (self.p1.x - self.p0.x).abs();
        let dy = -(self.p1.y - self.p0.y).abs();

        let sx = if self.p0.x < self.p1.x { 1 } else { -1 };
        let sy = if self.p0.y < self.p1.y { 1 } else { -1 };

        Bresenham {
            dx,
            dy,
            err: dx + dy,
            sx,
            sy,
            x0: self.p0.x,
            y0: self.p0.y,
            x1: self.p1.x,
            y1: self.p1.y,
            active: true,
        }
    }
}

fn parse_sweeps<T: BufRead>(lines: &mut Lines<T>) -> Vec<Sweep> {
    lines
        .filter_map(|l| l.ok())
        .map(|l| l.replace(" -> ", ","))
        .map(|l| Sweep::try_from(&l))
        .filter_map(|s| s.ok())
        .collect::<Vec<_>>()
}

fn accumulate(sweeps: &Vec<Sweep>) -> HashMap<Point, usize> {
    let mut acc = HashMap::new();
    sweeps
        .iter()
        .map(|sweep| sweep.points())
        .flatten()
        .for_each(|pt| {
            let count = acc.entry(pt).or_insert(0);
            *count += 1;
        });

    acc
}

fn hazard_points(map: &HashMap<Point, usize>) -> usize {
    map.iter()
        .filter_map(|entry| if *(entry.1) >= 2 { Some(entry.0) } else { None })
        .count()
}

fn main() -> Result<()> {
    let mut reader = BufReader::new(File::open("input")?);

    let sweeps = parse_sweeps(&mut reader.lines());

    let filtered_sweeps = sweeps
        .iter()
        .filter(|s| !s.is_diagonal())
        .cloned()
        .collect::<Vec<Sweep>>();

    let acc = accumulate(&filtered_sweeps);
    dbg!(hazard_points(&acc));

    // part 2
    let acc = accumulate(&sweeps);
    dbg!(hazard_points(&acc));

    Ok(())
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::io::Cursor;

    const INPUT: &str = r#"0,9 -> 5,9
8,0 -> 0,8
9,4 -> 3,4
2,2 -> 2,1
7,0 -> 7,4
6,4 -> 2,0
0,9 -> 2,9
3,4 -> 1,4
0,0 -> 8,8
5,5 -> 8,2
"#;

    #[test]
    fn test_sweeps_parse() -> Result<()> {
        let mut lines = Cursor::new(INPUT).lines();

        let sweeps = parse_sweeps(&mut lines);

        assert_eq!(sweeps.len(), 9);
        assert_eq!(sweeps[2].p0, Point { x: 9, y: 4 });

        Ok(())
    }

    #[test]
    fn test_sweep_bresenham() -> Result<()> {
        let s = Sweep {
            p0: Point { x: 0, y: 0 },
            p1: Point { x: 3, y: 3 },
        };

        let pts = s.points().map(|p| (p.x, p.y)).collect::<Vec<_>>();

        assert_eq!(pts, vec![(0, 0), (1, 1), (2, 2), (3, 3)]);

        Ok(())
    }

    #[test]
    fn test_accumulate() -> Result<()> {
        let mut lines = Cursor::new(INPUT).lines();
        let sweeps = parse_sweeps(&mut lines)
            .iter()
            .filter(|s| !s.is_diagonal())
            .cloned()
            .collect::<Vec<Sweep>>();

        let acc = accumulate(&sweeps);

        assert_eq!(hazard_points(&acc), 5);

        Ok(())
    }

    #[test]
    fn test_accumulate_diag() -> Result<()> {
        let mut lines = Cursor::new(INPUT).lines();
        let sweeps = parse_sweeps(&mut lines);

        let acc = accumulate(&sweeps);

        assert_eq!(hazard_points(&acc), 12);

        Ok(())
    }
}
