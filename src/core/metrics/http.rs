//! Minimal HTTP responder for Prometheus scraping. Zero deps beyond std::net.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use super::LatencyHistogram;

/// HTTP server for Prometheus metrics endpoint.
pub struct MetricsServer {
    shutdown: Arc<AtomicBool>,
    handle: Option<thread::JoinHandle<()>>,
}

impl MetricsServer {
    /// Spawn HTTP server on given address. Serves GET /metrics.
    pub fn spawn(
        bind_addr: &str,
        admission_histogram: Arc<LatencyHistogram>,
        persistence_histogram: Option<Arc<LatencyHistogram>>,
    ) -> std::io::Result<Self> {
        let listener = TcpListener::bind(bind_addr)?;
        listener.set_nonblocking(true)?;

        let shutdown = Arc::new(AtomicBool::new(false));
        let shutdown_clone = shutdown.clone();

        let handle = thread::spawn(move || {
            Self::run_loop(listener, admission_histogram, persistence_histogram, shutdown_clone);
        });

        Ok(Self {
            shutdown,
            handle: Some(handle),
        })
    }

    fn run_loop(
        listener: TcpListener,
        admission: Arc<LatencyHistogram>,
        persistence: Option<Arc<LatencyHistogram>>,
        shutdown: Arc<AtomicBool>,
    ) {
        let mut request_buf = [0u8; 1024];

        while !shutdown.load(Ordering::Relaxed) {
            match listener.accept() {
                Ok((mut stream, _)) => {
                    let _ = stream.set_read_timeout(Some(Duration::from_millis(100)));
                    let _ = stream.set_write_timeout(Some(Duration::from_millis(100)));

                    if let Ok(n) = stream.read(&mut request_buf) {
                        if n > 0 {
                            Self::handle_request(&mut stream, &request_buf[..n], &admission, &persistence);
                        }
                    }
                }
                Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(10));
                }
                Err(_) => {
                    thread::sleep(Duration::from_millis(10));
                }
            }
        }
    }

    fn handle_request(
        stream: &mut TcpStream,
        request: &[u8],
        admission: &LatencyHistogram,
        persistence: &Option<Arc<LatencyHistogram>>,
    ) {
        let request_str = String::from_utf8_lossy(request);

        // Only handle GET /metrics
        if !request_str.starts_with("GET /metrics") {
            let response = "HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n";
            let _ = stream.write_all(response.as_bytes());
            return;
        }

        let body = Self::render_metrics(admission, persistence);
        let response = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/plain; version=0.0.4\r\nContent-Length: {}\r\n\r\n{}",
            body.len(),
            body
        );
        let _ = stream.write_all(response.as_bytes());
    }

    fn render_metrics(
        admission: &LatencyHistogram,
        persistence: &Option<Arc<LatencyHistogram>>,
    ) -> String {
        let mut out = String::with_capacity(8192);

        // Admission latency histogram
        Self::render_histogram(&mut out, "ctfs_admission_latency", admission);

        // Persistence latency histogram (if available)
        if let Some(ref persist) = persistence {
            Self::render_histogram(&mut out, "ctfs_persistence_latency", persist);
        }

        out
    }

    fn render_histogram(out: &mut String, name: &str, hist: &LatencyHistogram) {
        let buckets = hist.snapshot();
        let mut cumulative = 0u64;

        out.push_str(&format!("# HELP {}_bucket {} latency histogram (ns)\n", name, name));
        out.push_str(&format!("# TYPE {}_bucket histogram\n", name));

        for i in 0..64 {
            cumulative += buckets[i];
            let le = LatencyHistogram::bucket_le(i);
            if le == u64::MAX {
                out.push_str(&format!("{}_bucket{{le=\"+Inf\"}} {}\n", name, cumulative));
            } else {
                out.push_str(&format!("{}_bucket{{le=\"{}\"}} {}\n", name, le, cumulative));
            }
        }

        let total = hist.total();
        out.push_str(&format!("{}_count {}\n", name, total));

        let (p50, p90, p99) = hist.percentiles();
        out.push_str(&format!("{}_p50 {}\n", name, p50));
        out.push_str(&format!("{}_p90 {}\n", name, p90));
        out.push_str(&format!("{}_p99 {}\n", name, p99));
    }

    /// Shutdown the server.
    pub fn shutdown(&mut self) {
        self.shutdown.store(true, Ordering::Relaxed);
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

impl Drop for MetricsServer {
    fn drop(&mut self) {
        self.shutdown();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_render_histogram() {
        let hist = LatencyHistogram::new();
        hist.record(100);
        hist.record(200);

        let mut out = String::new();
        MetricsServer::render_histogram(&mut out, "test_latency", &hist);

        assert!(out.contains("test_latency_bucket"));
        assert!(out.contains("test_latency_count 2"));
        assert!(out.contains("test_latency_p50"));
    }
}
