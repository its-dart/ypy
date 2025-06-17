[![PyPI version](https://badge.fury.io/py/y-py.svg)](https://badge.fury.io/py/y-py)

# Ypy

**Python bindings for Y-CRDT** - Build real-time collaborative applications with distributed data types.

Ypy provides Python bindings for [Y-CRDT](https://github.com/y-crdt/y-crdt) (Yjs Conflict-free Replicated Data Types), enabling real-time collaboration between devices and platforms. Whether you're building collaborative text editors, shared whiteboards, or any application requiring real-time synchronization, Ypy offers the performance of Rust with the simplicity of Python.

## ✨ Key Features

- **Real-time collaboration**: Sync data seamlessly across devices and platforms
- **Cross-platform compatibility**: Works with any Y-CRDT implementation (Yjs, Yrs, etc.)
- **High performance**: Built on [Yrs](https://github.com/y-crdt/y-crdt) (Rust) for speed and safety
- **Familiar API**: Similar to [Yjs](https://docs.yjs.dev/) for easy adoption
- **Python 3.7+**: Supports Python 3.7 through 3.12

## 📚 Documentation

- [API Documentation](docs/)
- [Examples](examples/)
- [Y-CRDT Documentation](https://docs.yjs.dev/)

---

> **Note**: [We are looking for a maintainer 👀](https://github.com/y-crdt/ypy/issues/148) - interested in contributing to this project?

## Installation

```
pip install y-py
```

## 🚀 Quick Start

Ypy provides distributed data types similar to [Yjs](https://docs.yjs.dev/). All data is shared within a `YDoc` and modified within transaction blocks for consistency.

```python
import y_py as Y

# Create a document and add some text
doc1 = Y.YDoc()
text = doc1.get_text('my-text')

with doc1.begin_transaction() as txn:
    text.extend(txn, "Hello, collaborative world!")

# Create a second document and sync the state
doc2 = Y.YDoc()
state_vector = Y.encode_state_vector(doc2)
diff = Y.encode_state_as_update(doc1, state_vector)
Y.apply_update(doc2, diff)

# Both documents now have the same content
print(str(doc2.get_text('my-text')))  # "Hello, collaborative world!"
```

### Available Data Types

- **YText**: Collaborative text editing
- **YArray**: Shared arrays
- **YMap**: Shared key-value maps
- **YXmlElement**: Collaborative XML/HTML editing

For more examples, see the [examples directory](examples/).

## 🛠️ Development

### Prerequisites

1. Install [Rust](https://www.rust-lang.org/tools/install) and [Python](https://www.python.org/downloads/) 3.7+
2. Install `maturin` for building: `pip install maturin`

### Setup

```bash
# Clone the repository
git clone https://github.com/y-crdt/ypy.git
cd ypy

# Create a development build
maturin develop

# Run tests
pip install pytest
pytest
```

### Using Hatch (Recommended)

For testing across multiple Python versions:

```bash
# Install dependencies and build for all Python versions
hatch run test:maturin develop

# Run tests across all supported Python versions (3.7-3.12)
hatch run test:pytest
```

### Building

Build wheel packages:

```bash
maturin build  # Output: target/wheels/
```

## 🌐 WASM Support (Pyodide)

Ypy supports WebAssembly through Pyodide for browser-based Python environments. Since PyPI doesn't host WASM wheels, they're available as release assets.

**Quick Setup:**
```python
# In Pyodide environment
import micropip
wheel_url = "https://github.com/y-crdt/ypy/releases/latest"  # Check releases for specific wheel
# Use a CORS proxy to install: https://api.allorigins.win/raw?url={wheel_url}
```

**Try it now:** [Pyodide Terminal](https://pyodide.org/en/stable/console.html)

For detailed WASM setup instructions, see our [WASM Guide](docs/) or check the [latest releases](https://github.com/y-crdt/ypy/releases) for wheel downloads.

---

## 🤝 Contributing

We welcome contributions! Please see our [development setup](#-development) above to get started.

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## 🔗 Related Projects

- [Y-CRDT](https://github.com/y-crdt/y-crdt) - The core Rust implementation
- [Yjs](https://github.com/yjs/yjs) - JavaScript Y-CRDT implementation  
- [ypy-websocket](https://github.com/y-crdt/ypy-websocket) - WebSocket provider for Ypy
