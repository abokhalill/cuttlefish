//! Prometheus exposition. Scrapes atomics, spits text format.

use super::LatencyHistogram;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

/// Prometheus text format exporter.
pub struct PrometheusExporter {
    histogram: Arc<LatencyHistogram>,
    prefix: &'static str,
}

impl PrometheusExporter {
    pub fn new(histogram: Arc<LatencyHistogram>, prefix: &'static str) -> Self {
        Self { histogram, prefix }
    }

    /// Format histogram as Prometheus text exposition.
    pub fn render(&self) -> String {
        let mut out = String::with_capacity(4096);
        let buckets = self.histogram.snapshot();
        let mut cumulative = 0u64;

        out.push_str(&format!(
            "# HELP {}_admission_latency_bucket Admission latency histogram\n",
            self.prefix
        ));
        out.push_str(&format!(
            "# TYPE {}_admission_latency_bucket histogram\n",
            self.prefix
        ));

        for i in 0..64 {
            cumulative += buckets[i];
            let le = LatencyHistogram::bucket_le(i);
            if le == u64::MAX {
                out.push_str(&format!(
                    "{}_admission_latency_bucket{{le=\"+Inf\"}} {}\n",
                    self.prefix, cumulative
                ));
            } else {
                out.push_str(&format!(
                    "{}_admission_latency_bucket{{le=\"{}\"}} {}\n",
                    self.prefix, le, cumulative
                ));
            }
        }

        let total = self.histogram.total();
        out.push_str(&format!(
            "{}_admission_latency_count {}\n",
            self.prefix, total
        ));

        let (p50, p90, p99) = self.histogram.percentiles();
        out.push_str(&format!(
            "# HELP {}_admission_latency_p50 50th percentile latency (ns)\n",
            self.prefix
        ));
        out.push_str(&format!(
            "# TYPE {}_admission_latency_p50 gauge\n",
            self.prefix
        ));
        out.push_str(&format!(
            "{}_admission_latency_p50 {}\n",
            self.prefix, p50
        ));

        out.push_str(&format!(
            "{}_admission_latency_p90 {}\n",
            self.prefix, p90
        ));
        out.push_str(&format!(
            "{}_admission_latency_p99 {}\n",
            self.prefix, p99
        ));

        out
    }
}

/// Background scraper thread. Periodically snapshots and stores rendered output.
pub struct MetricsScraper {
    handle: Option<thread::JoinHandle<()>>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
    output: Arc<std::sync::RwLock<String>>,
}

impl MetricsScraper {
    /// Spawn scraper thread. Interval in milliseconds.
    pub fn spawn(histogram: Arc<LatencyHistogram>, prefix: &'static str, interval_ms: u64) -> Self {
        let shutdown = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let output = Arc::new(std::sync::RwLock::new(String::new()));

        let shutdown_clone = shutdown.clone();
        let output_clone = output.clone();

        let handle = thread::spawn(move || {
            let exporter = PrometheusExporter::new(histogram, prefix);
            let interval = Duration::from_millis(interval_ms);

            while !shutdown_clone.load(std::sync::atomic::Ordering::Relaxed) {
                let rendered = exporter.render();
                if let Ok(mut guard) = output_clone.write() {
                    *guard = rendered;
                }
                thread::sleep(interval);
            }
        });

        Self {
            handle: Some(handle),
            shutdown,
            output,
        }
    }

    /// Get latest rendered metrics.
    pub fn get(&self) -> String {
        self.output
            .read()
            .map(|g| g.clone())
            .unwrap_or_default()
    }

    /// Shutdown the scraper thread.
    pub fn shutdown(&mut self) {
        self.shutdown
            .store(true, std::sync::atomic::Ordering::Relaxed);
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

impl Drop for MetricsScraper {
    fn drop(&mut self) {
        self.shutdown();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prometheus_render() {
        let h = Arc::new(LatencyHistogram::new());
        h.record(100);
        h.record(200);
        h.record(1000);

        let exporter = PrometheusExporter::new(h, "ctfs");
        let output = exporter.render();

        assert!(output.contains("ctfs_admission_latency_bucket"));
        assert!(output.contains("ctfs_admission_latency_count 3"));
        assert!(output.contains("ctfs_admission_latency_p50"));
    }

    #[test]
    fn test_scraper_lifecycle() {
        let h = Arc::new(LatencyHistogram::new());
        h.record(50);

        let mut scraper = MetricsScraper::spawn(h, "ctfs", 10);
        thread::sleep(Duration::from_millis(50));

        let output = scraper.get();
        assert!(output.contains("ctfs_admission_latency_count 1"));

        scraper.shutdown();
    }
}
