pub struct DWave {
    annealing_time: float, // in microseconds
    num_runs: i32, 
}

impl DWave {
    pub fn new(annealing_time: float, num_runs: i32) -> Self{
        Self {
            annealing_time: annealing_time,
            num_runs: num_runs
        }
    }

    
}

