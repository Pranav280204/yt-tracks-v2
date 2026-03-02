"""WSGI entrypoint compatibility module for Gunicorn deployments."""

from app import app

__all__ = ["app"]
