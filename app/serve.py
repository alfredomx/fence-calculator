"""Dev server for the fence calculator: static files with caching disabled,
so the browser always picks up the latest JS/CSS without hard refreshes."""
import os
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler

os.chdir(os.path.dirname(os.path.abspath(__file__)))


class NoCacheHandler(SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header('Cache-Control', 'no-store, must-revalidate')
        self.send_header('Expires', '0')
        super().end_headers()


if __name__ == '__main__':
    print('Serving on http://localhost:8123 (no-cache)')
    ThreadingHTTPServer(('', 8123), NoCacheHandler).serve_forever()
