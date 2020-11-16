use crate::*;

pub fn transpose(a: &Vec<Expr>) -> Result<Expr, Error> {
    let mut res = vec![];
    let cols = if let Some(a) = a.get(0) {
        if let List(a) = a {
            a.len()
        } else {
            return Err(Error::InvalidComputation);
        }
    } else {
        return Err(Error::InvalidComputation);
    };
    if a.len() != cols {
        return Err(Error::InvalidComputation);
    }
    for i in 0..a.len() {
        let mut row = vec![];
        for j in 0..cols {
            if let Some(List(a)) = a.get(j) {
                if let Some(el) = a.get(i) {
                    row.push(el.clone());
                } else {
                    return Err(Error::InvalidComputation);
                }
            } else {
                return Err(Error::InvalidComputation);
            }
        }
        res.push(List(row));
    }
    Ok(List(res))
}

pub fn is_square_mat(a: &Vec<Expr>) -> Result<Expr, Error> {
    let n = a.len();
    let mut sq = true;
    for i in 0..n {
        if let List(b) = &a[i] {
            if b.len() != n {
                sq = false;
                break;
            }
        } else {
            sq = false;
            break;
        }
    }
    Ok(Ret(Bool(sq)))
}

pub fn dim(a: &Vec<Expr>) -> Result<Expr, Error> {
    let n = a.len();
    let mut m: Option<usize> = None;
    for i in 0..n {
        if let List(b) = &a[i] {
            if let Some(m) = m {
                if b.len() != m {
                    return Err(Error::InvalidComputation);
                }
            } else {
                m = Some(b.len());
            }
        } else {
            return Err(Error::InvalidComputation);
        }
    }
    if let Some(m) = m {
        Ok(List(vec![(n as f64).into(), (m as f64).into()]))
    } else {
        return Err(Error::InvalidComputation);
    }
}

pub fn col(a: f64, b: &Vec<Expr>) -> Result<Expr, Error> {
    let mut res = vec![];
    for bi in b {
        if let List(bi) = bi {
            if let Some(bi) = bi.get(a as usize) {
                res.push(bi.clone());
            } else {
                return Err(Error::InvalidComputation);
            }
        } else {
            return Err(Error::InvalidComputation);
        }
    }
    Ok(List(res))
}

pub fn mul_mat(a: &Vec<Expr>, b: &Vec<Expr>) -> Result<Expr, Error> {
    let mut res = vec![];
    let cols = if let Some(b) = b.get(0) {
        if let List(b) = b {
            b.len()
        } else {
            return Err(Error::InvalidComputation);
        }
    } else {
        return Err(Error::InvalidComputation);
    };
    for i in 0..a.len() {
        let mut row = vec![];
        for j in 0..cols {
            if let Some(a) = a.get(i) {
                row.push(app(Sum,
                    app2(Mul, a.clone(), col(j as f64, b)?)
                ));
            } else {
                return Err(Error::InvalidComputation);
            }
        }
        res.push(List(row));
    }
    Ok(List(res))
}
