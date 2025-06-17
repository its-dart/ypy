[![PyPI version](https://badge.fury.io/py/y-py.svg)](https://badge.fury.io/py/y-py)
[![Python versions](https://img.shields.io/pypi/pyversions/y-py.svg)](https://pypi.org/project/y-py/)

# Ypy

Ypy is a Python binding for Y-CRDT. It provides distributed data types that enable real-time collaboration between devices. Ypy can sync data with any other platform that has a Y-CRDT binding, allowing for seamless cross-domain communication. The library is a thin wrapper around Yrs, taking advantage of the safety and performance of Rust.

## Table of Contents

- [Installation](#installation)
- [Getting Started](#getting-started)
- [Documentation & Examples](#documentation--examples)
- [Development](#development)
- [WASM Support](#wasm-support)
- [Contributing](#contributing)

## Installation

```
pip install y-py
```

## Getting Started

Ypy provides many of the same shared data types as [Yjs](https://docs.yjs.dev/). All objects are shared within a `YDoc` and get modified within a transaction block.

```python
import y_py as Y

d1 = Y.YDoc()
# Create a new YText object in the YDoc
text = d1.get_text('test')
# Start a transaction in order to update the text
with d1.begin_transaction() as txn:
    # Add text contents
    text.extend(txn, "hello world!")

# Create another document
d2 = Y.YDoc()
# Share state with the original document
state_vector = Y.encode_state_vector(d2)
diff = Y.encode_state_as_update(d1, state_vector)
Y.apply_update(d2, diff)

value = str(d2.get_text('test'))

assert value == "hello world!"
```

## Documentation & Examples

- 📚 **[Full Documentation](docs/)** - Comprehensive guides and API reference
- 🎨 **[Examples](examples/)** - See Ypy in action with practical examples
  - [Drawing App Example](examples/drawing/) - Real-time collaborative drawing
- 🌐 **[Y-CRDT Ecosystem](https://docs.yjs.dev/)** - Learn about Y-CRDT and compatible libraries

## Development

### Prerequisites

- [Rust](https://www.rust-lang.org/tools/install)
- [Python](https://www.python.org/downloads/) (3.7+)

### Setup

1. Install `maturin` for building: `pip install maturin`
2. Create a development build: `maturin develop`

### Testing

```bash
pip install pytest
pytest
```

### Using Hatch (Optional)

For testing across multiple Python versions (3.7-3.12):

```bash
hatch run test:maturin develop
hatch run test:pytest
```

### Building

Build wheels for distribution:

```bash
maturin build
```

## WASM Support

Ypy supports WebAssembly through Pyodide, but requires special installation due to PyPI limitations with `emscripten` wheels.

### Installation in Pyodide

1. Download the WASM wheel from [Releases](https://github.com/y-crdt/ypy/releases)
2. Use a CORS proxy to install (due to GitHub's CORS restrictions)

```python
# Example installation in Pyodide
import pyodide
wheel_url = 'https://github.com/y-crdt/ypy/releases/download/v0.5.5/y_py-0.5.5-cp310-cp310-emscripten_3_1_14_wasm32.whl'
proxy_url = f'https://api.allorigins.win/raw?url={wheel_url}'
resp = await pyodide.http.pyfetch(proxy_url)
content = await resp.bytes()

with open('y_py.whl', 'wb') as f:
    f.write(content)

import micropip
await micropip.install('emfs:./y_py.whl')

# Now you can use Ypy normally
import y_py as Y
```

Try it out at [pyodide.org/console](https://pyodide.org/en/stable/console.html)!

## Contributing

We welcome contributions! Please see our development setup above to get started.

> **Note**: [We are looking for a maintainer 👀](https://github.com/y-crdt/ypy/issues/148) - if you're interested in helping maintain this project, please reach out!

## Links

- [PyPI Package](https://pypi.org/project/y-py/)
- [GitHub Repository](https://github.com/y-crdt/ypy)
- [Issue Tracker](https://github.com/y-crdt/ypy/issues)
- [Y-CRDT Documentation](https://docs.yjs.dev/)
