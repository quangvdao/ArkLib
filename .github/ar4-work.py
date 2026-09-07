"""Reviewed, idempotent edits for the isolated AR-4 validation branch only."""
from pathlib import Path
import re

version = "ar4-source-levels-v1"
marker = Path('.github/ar4-applied.txt')
if not marker.exists() or marker.read_text().strip() != version:
    for name in ('ArkLib/Interaction/Oracle/Source.lean',
                 'ArkLibTest/Interaction/Oracle/SourceExample.lean'):
        path = Path(name)
        text = path.read_text()
        def reorder(match):
            args = [arg.strip() for arg in match.group(2).split(',')]
            assert len(args) in (3, 4), (name, match.group(0))
            args[1], args[2] = args[2], args[1]
            return match.group(1) + '.{' + ', '.join(args) + '}'
        text = re.sub(r'(SourceCtx|liftResponse)\.\{([^}]+)\}', reorder, text)
        text = text.replace(
            'The carriers are explicit parameters, so query, response, and environment universes stay independent.',
            'The carriers are explicit parameters: query, response, and environment universes\nstay independent.')
        path.write_text(text)
    marker.write_text(version + '\n')
