#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Gerenciador de Infraestrutura de TI (multiempresa)  -  v3 (com Base de Conhecimento)
=============================================================================

Tecnologias: Python 3.9+, Tkinter/ttk e SQLite. Somente biblioteca padrão:
NÃO exige nenhuma instalação via pip.

ONDE OS DADOS SÃO SALVOS
------------------------
Tudo fica em  ./data/infra.db  (pasta "data" ao lado deste arquivo; se o
programa for empacotado com PyInstaller, ao lado do .exe).
Tabelas:
  - usuarios    : login + HASH scrypt da senha + chave do cofre (embrulhada)
  - empresas    : nome de cada empresa
  - ativos      : servidores/estações (FK -> empresas, remoção em cascata)
  - credenciais : e-mails, logins e senhas por empresa (FK -> empresas)
  - manual_blocos : categorias da Base de Conhecimento (Redes e VPNs, Impressoras...)
  - manuais       : manuais de cada bloco (caminho do arquivo/link e/ou conteúdo)
  - meta          : marcadores internos (ex.: blocos iniciais já criados)
Erros inesperados são gravados em ./data/erro.log.

SEGURANÇA
---------
1) Senha de ACESSO ao programa
   - Nunca é gravada. Gravamos só o hash scrypt (função "memory-hard",
     equivalente em robustez ao bcrypt) com salt aleatório de 16 bytes:
         scrypt$N$r$p$<salt_b64>$<hash_b64>
   - No login o hash é recalculado e comparado em tempo constante
     (hmac.compare_digest).

2) Senhas de E-MAIL/CREDENCIAIS (tabela "credenciais")
   - Estas senhas precisam ser LEGÍVEIS (o helpdesk copia e usa), então não
     dá para usar hash. Por isso são CRIPTOGRAFADAS, nunca guardadas em
     texto limpo:
       * Existe uma chave de dados aleatória de 32 bytes (o "cofre").
       * O cofre fica no banco "embrulhado" por uma chave derivada da SUA
         senha de login (scrypt + salt próprio). Sem a senha de login, o
         arquivo infra.db não revela as senhas das contas.
       * Cada senha é cifrada com HMAC-SHA256 em modo contador (cifra de
         fluxo) + etiqueta HMAC-SHA256 (encrypt-then-MAC), nonce aleatório
         de 16 bytes. Qualquer adulteração é detectada ao decifrar.
       * O cofre só é aberto na memória após o login e descartado no logout.
   - ATENÇÃO: se a senha de login for esquecida, as senhas do cofre NÃO
     podem ser recuperadas. Use "Configurações > Alterar senha" para trocar
     a senha sem perder dados (o cofre é re-embrulhado).
   - Obs.: sem bibliotecas externas não há AES na biblioteca padrão; a
     construção acima usa somente primitivas padrão (hmac/hashlib/os.urandom).
     IPs, hostnames, e-mails e logins ficam legíveis no SQLite; para proteger
     o arquivo inteiro em disco use BitLocker ou SQLCipher.

3) Área de transferência
   - Senhas copiadas são removidas da área de transferência após 30 s
     (se ainda forem o conteúdo atual) e ao sair da conta.

4) Manuais de Apoio (Base de Conhecimento)
   - Cada manual guarda o CAMINHO de um arquivo na rede, um link http(s) e/ou um
     texto com o passo a passo. Não coloque senhas nos manuais: eles ficam em
     texto legível no SQLite (use a aba E-mails e Credenciais, que é criptografada).
   - Por segurança, o botão Abrir recusa executáveis/scripts (.exe, .bat, .ps1,
     .lnk...) e links que não sejam http/https, mesmo que alguém altere o banco.

Execução:  python infra_manager.py
"""

import base64
import hashlib
import hmac
import ipaddress
import os
import re
import secrets
import sqlite3
import string
import subprocess
import sys
import tkinter as tk
import webbrowser
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

# --------------------------------------------------------------------------
# Caminhos
# --------------------------------------------------------------------------
if getattr(sys, "frozen", False):
    BASE_DIR = Path(sys.executable).resolve().parent
else:
    BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"          # pasta específica do sistema
DB_PATH = DATA_DIR / "infra.db"       # arquivo do banco SQLite
ERROR_LOG = DATA_DIR / "erro.log"

# --------------------------------------------------------------------------
# Segurança: hash de senhas (scrypt) e cofre de credenciais
# --------------------------------------------------------------------------
SCRYPT_N = 2 ** 14   # custo de CPU/memória (16 MB por hash)
SCRYPT_R = 8
SCRYPT_P = 1
SCRYPT_DKLEN = 32
MIN_PASSWORD_LEN = 8
CLIPBOARD_CLEAR_MS = 30_000


def _b64(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def _unb64(text: str) -> bytes:
    return base64.b64decode(text.encode("ascii"))


def hash_password(password: str) -> str:
    """Gera 'scrypt$N$r$p$salt$hash'. É isto (e só isto) que vai ao banco."""
    salt = os.urandom(16)
    digest = hashlib.scrypt(
        password.encode("utf-8"), salt=salt,
        n=SCRYPT_N, r=SCRYPT_R, p=SCRYPT_P, dklen=SCRYPT_DKLEN,
    )
    return f"scrypt${SCRYPT_N}${SCRYPT_R}${SCRYPT_P}${_b64(salt)}${_b64(digest)}"


def verify_password(password: str, stored: str) -> bool:
    """Recalcula o hash com o salt salvo e compara em tempo constante."""
    try:
        algo, n, r, p, salt_b64, hash_b64 = stored.split("$")
        if algo != "scrypt":
            return False
        salt = _unb64(salt_b64)
        expected = _unb64(hash_b64)
        candidate = hashlib.scrypt(
            password.encode("utf-8"), salt=salt,
            n=int(n), r=int(r), p=int(p), dklen=len(expected),
        )
        return hmac.compare_digest(candidate, expected)
    except (ValueError, TypeError):
        return False


# Hash "falso" usado quando o usuário não existe, para que o tempo de resposta
# seja o mesmo e não revele se o nome de usuário é válido.
_DUMMY_HASH = hash_password("dummy-password-not-used")


def _derive_key(password: str, salt: bytes, n=SCRYPT_N, r=SCRYPT_R, p=SCRYPT_P) -> bytes:
    """Deriva uma chave de 32 bytes a partir da senha (scrypt)."""
    return hashlib.scrypt(password.encode("utf-8"), salt=salt, n=n, r=r, p=p, dklen=32)


def _subkeys(key: bytes):
    """Separa a chave em duas (cifra e autenticação) - separação de domínio."""
    return (hmac.new(key, b"enc", hashlib.sha256).digest(),
            hmac.new(key, b"mac", hashlib.sha256).digest())


def _keystream_xor(enc_key: bytes, nonce: bytes, data: bytes) -> bytes:
    """Cifra de fluxo: HMAC-SHA256(chave, nonce || contador) em blocos de 32 bytes."""
    out = bytearray()
    for i in range(0, len(data), 32):
        block = hmac.new(enc_key, nonce + (i // 32).to_bytes(8, "big"), hashlib.sha256).digest()
        out.extend(b ^ k for b, k in zip(data[i:i + 32], block))
    return bytes(out)


def encrypt_bytes(key: bytes, data: bytes) -> bytes:
    """nonce(16) + texto cifrado + etiqueta HMAC(32)."""
    enc_key, mac_key = _subkeys(key)
    nonce = os.urandom(16)
    ciphertext = _keystream_xor(enc_key, nonce, data)
    tag = hmac.new(mac_key, b"v1" + nonce + ciphertext, hashlib.sha256).digest()
    return nonce + ciphertext + tag


def decrypt_bytes(key: bytes, blob: bytes) -> bytes:
    """Verifica a etiqueta ANTES de decifrar. ValueError se inválido/adulterado."""
    if len(blob) < 48:
        raise ValueError("Dado criptografado inválido.")
    nonce, ciphertext, tag = blob[:16], blob[16:-32], blob[-32:]
    enc_key, mac_key = _subkeys(key)
    expected = hmac.new(mac_key, b"v1" + nonce + ciphertext, hashlib.sha256).digest()
    if not hmac.compare_digest(tag, expected):
        raise ValueError("Falha de autenticação (chave incorreta ou dado adulterado).")
    return _keystream_xor(enc_key, nonce, ciphertext)


def encrypt_text(key: bytes, text: str) -> str:
    return "v1:" + _b64(encrypt_bytes(key, text.encode("utf-8")))


def decrypt_text(key: bytes, token: str) -> str:
    if not token.startswith("v1:"):
        raise ValueError("Formato de dado criptografado desconhecido.")
    return decrypt_bytes(key, _unb64(token[3:])).decode("utf-8")


def wrap_vault_key(vault_key: bytes, password: str) -> str:
    """Embrulha a chave do cofre com uma chave derivada da senha de login."""
    salt = os.urandom(16)
    kek = _derive_key(password, salt)
    return (f"v1${SCRYPT_N}${SCRYPT_R}${SCRYPT_P}${_b64(salt)}$"
            f"{_b64(encrypt_bytes(kek, vault_key))}")


def unwrap_vault_key(wrapped: str, password: str) -> bytes:
    parts = wrapped.split("$")
    if len(parts) != 6 or parts[0] != "v1":
        raise ValueError("Cofre em formato desconhecido.")
    n, r, p = int(parts[1]), int(parts[2]), int(parts[3])
    kek = _derive_key(password, _unb64(parts[4]), n, r, p)
    return decrypt_bytes(kek, _unb64(parts[5]))


def generate_password(length: int = 16) -> str:
    """Senha forte aleatória (secrets), com ao menos 1 de cada tipo."""
    groups = [string.ascii_lowercase, string.ascii_uppercase, string.digits, "!@#$%&*?-_"]
    chars = [secrets.choice(g) for g in groups]
    pool = "".join(groups)
    chars += [secrets.choice(pool) for _ in range(length - len(chars))]
    secrets.SystemRandom().shuffle(chars)
    return "".join(chars)


# --------------------------------------------------------------------------
# Camada de banco de dados
# --------------------------------------------------------------------------
SCHEMA = """
CREATE TABLE IF NOT EXISTS usuarios (
    id            INTEGER PRIMARY KEY AUTOINCREMENT,
    username      TEXT NOT NULL UNIQUE COLLATE NOCASE,
    password_hash TEXT NOT NULL,              -- NUNCA texto limpo
    wrapped_key   TEXT,                       -- chave do cofre, embrulhada
    criado_em     TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);
CREATE TABLE IF NOT EXISTS empresas (
    id    INTEGER PRIMARY KEY AUTOINCREMENT,
    nome  TEXT NOT NULL UNIQUE COLLATE NOCASE
);
CREATE TABLE IF NOT EXISTS ativos (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    empresa_id  INTEGER NOT NULL REFERENCES empresas(id) ON DELETE CASCADE,
    hostname    TEXT NOT NULL COLLATE NOCASE,
    ip          TEXT DEFAULT '',
    wireguard   TEXT DEFAULT '',
    openvpn     TEXT DEFAULT '',
    anydesk     TEXT DEFAULT '',
    funcao      TEXT DEFAULT '',
    estrutura   TEXT DEFAULT '',
    modelo_so   TEXT DEFAULT '',
    UNIQUE (empresa_id, hostname)
);
CREATE INDEX IF NOT EXISTS idx_ativos_empresa ON ativos(empresa_id);
CREATE TABLE IF NOT EXISTS credenciais (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    empresa_id  INTEGER NOT NULL REFERENCES empresas(id) ON DELETE CASCADE,
    servico     TEXT DEFAULT '',
    email       TEXT NOT NULL,
    login       TEXT DEFAULT '',
    senha_enc   TEXT DEFAULT '',              -- senha CRIPTOGRAFADA (v1:...)
    obs         TEXT DEFAULT ''
);
CREATE INDEX IF NOT EXISTS idx_cred_empresa ON credenciais(empresa_id);
CREATE TABLE IF NOT EXISTS meta (
    chave  TEXT PRIMARY KEY,
    valor  TEXT
);
CREATE TABLE IF NOT EXISTS manual_blocos (
    id     INTEGER PRIMARY KEY AUTOINCREMENT,
    nome   TEXT NOT NULL UNIQUE COLLATE NOCASE,
    ordem  INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS manuais (
    id             INTEGER PRIMARY KEY AUTOINCREMENT,
    bloco_id       INTEGER NOT NULL REFERENCES manual_blocos(id) ON DELETE CASCADE,
    titulo         TEXT NOT NULL COLLATE NOCASE,
    caminho        TEXT DEFAULT '',          -- arquivo na rede ou link http(s)
    conteudo       TEXT DEFAULT '',          -- descrição / passo a passo
    atualizado_em  TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    UNIQUE (bloco_id, titulo)
);
CREATE INDEX IF NOT EXISTS idx_manuais_bloco ON manuais(bloco_id);
"""

ASSET_FIELDS = ["hostname", "ip", "wireguard", "openvpn",
                "anydesk", "funcao", "estrutura", "modelo_so"]
CRED_FIELDS = ["servico", "email", "login", "obs"]   # + senha (criptografada)

# Pares (tabela, coluna) permitidos para o histórico de autocompletar.
_HISTORY_SOURCES = {
    ("ativos", "funcao"), ("ativos", "modelo_so"),
    ("ativos", "wireguard"), ("ativos", "openvpn"),
    ("credenciais", "servico"),
}

# Blocos criados na primeira vez (uma única vez: apagar todos não os recria).
DEFAULT_MANUAL_BLOCKS = ["Redes e VPNs", "Servidores & Active Directory",
                         "Impressoras", "Softwares & Pacote Office"]


def _like(term: str) -> str:
    esc = term.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
    return f"%{esc}%"


class Database:
    def __init__(self, path: Path):
        self.path = Path(path)
        self.conn = None
        self.vault_key = None      # chave do cofre: só existe na memória, após o login

    # ---- inicialização ----------------------------------------------------
    def _connect(self):
        self.conn = sqlite3.connect(self.path)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA foreign_keys = ON")   # habilita cascade

    def _migrate(self):
        """Cria tabelas novas e atualiza bancos da versão 1 (sem perder dados)."""
        self.conn.executescript(SCHEMA)
        cols = [r["name"] for r in self.conn.execute("PRAGMA table_info(usuarios)")]
        if "wrapped_key" not in cols:
            self.conn.execute("ALTER TABLE usuarios ADD COLUMN wrapped_key TEXT")
        # Blocos iniciais da Base de Conhecimento (só na primeira migração).
        if self.conn.execute("SELECT 1 FROM meta WHERE chave = 'manuais_seed'").fetchone() is None:
            for pos, nome in enumerate(DEFAULT_MANUAL_BLOCKS, start=1):
                self.conn.execute("INSERT OR IGNORE INTO manual_blocos (nome, ordem) VALUES (?, ?)",
                                  (nome, pos))
            self.conn.execute("INSERT INTO meta (chave, valor) VALUES ('manuais_seed', '1')")
        self.conn.commit()

    def is_ready(self) -> bool:
        """True se a pasta/arquivo existem e já há ao menos um usuário."""
        if not self.path.exists():      # checar ANTES: connect() cria o arquivo
            return False
        try:
            if self.conn is None:
                self._connect()
            self._migrate()
            return self.conn.execute("SELECT COUNT(*) FROM usuarios").fetchone()[0] > 0
        except sqlite3.Error:
            return False

    def initialize(self):
        """Cria a pasta, o arquivo .db e as tabelas (primeiro acesso)."""
        self.path.parent.mkdir(parents=True, exist_ok=True)
        if self.conn is None:
            self._connect()
        self._migrate()

    # ---- usuários e cofre -------------------------------------------------
    def create_user(self, username: str, password: str):
        vault_key = os.urandom(32)
        self.conn.execute(
            "INSERT INTO usuarios (username, password_hash, wrapped_key) VALUES (?, ?, ?)",
            (username.strip(), hash_password(password), wrap_vault_key(vault_key, password)),
        )
        self.conn.commit()

    def login(self, username: str, password: str) -> bool:
        """Valida a senha e abre o cofre (self.vault_key) na memória."""
        row = self.conn.execute(
            "SELECT id, password_hash, wrapped_key FROM usuarios WHERE username = ?",
            (username.strip(),),
        ).fetchone()
        if row is None:
            verify_password(password, _DUMMY_HASH)   # equaliza o tempo
            return False
        if not verify_password(password, row["password_hash"]):
            return False
        try:
            if row["wrapped_key"]:
                self.vault_key = unwrap_vault_key(row["wrapped_key"], password)
            else:
                # Banco da versão 1: cria o cofre agora, protegido pela senha atual.
                self.vault_key = os.urandom(32)
                self.conn.execute("UPDATE usuarios SET wrapped_key = ? WHERE id = ?",
                                  (wrap_vault_key(self.vault_key, password), row["id"]))
                self.conn.commit()
        except ValueError:
            self.vault_key = None
            return False
        return True

    def logout(self):
        self.vault_key = None

    def change_password(self, username: str, old: str, new: str):
        """Troca a senha e re-embrulha o cofre (as credenciais continuam legíveis)."""
        row = self.conn.execute(
            "SELECT id, password_hash, wrapped_key FROM usuarios WHERE username = ?",
            (username.strip(),),
        ).fetchone()
        if row is None or not verify_password(old, row["password_hash"]):
            raise ValueError("A senha atual está incorreta.")
        vault_key = (unwrap_vault_key(row["wrapped_key"], old)
                     if row["wrapped_key"] else os.urandom(32))
        with self.conn:      # transação: tudo ou nada
            self.conn.execute(
                "UPDATE usuarios SET password_hash = ?, wrapped_key = ? WHERE id = ?",
                (hash_password(new), wrap_vault_key(vault_key, new), row["id"]))
        self.vault_key = vault_key

    def _seal(self, plain: str) -> str:
        if not plain:
            return ""
        if self.vault_key is None:
            raise RuntimeError("Cofre bloqueado: faça login novamente.")
        return encrypt_text(self.vault_key, plain)

    def reveal(self, token: str) -> str:
        """Decifra uma senha do cofre. ValueError se corrompida."""
        if not token:
            return ""
        if self.vault_key is None:
            raise RuntimeError("Cofre bloqueado: faça login novamente.")
        return decrypt_text(self.vault_key, token)

    # ---- empresas -----------------------------------------------------------
    def list_companies(self):
        return self.conn.execute(
            "SELECT id, nome FROM empresas ORDER BY nome COLLATE NOCASE").fetchall()

    def list_companies_with_counts(self):
        return self.conn.execute(
            """SELECT e.id, e.nome,
                      (SELECT COUNT(*) FROM ativos a WHERE a.empresa_id = e.id) AS ativos,
                      (SELECT COUNT(*) FROM credenciais c WHERE c.empresa_id = e.id) AS contas
                 FROM empresas e ORDER BY e.nome COLLATE NOCASE""").fetchall()

    def get_company(self, company_id: int):
        return self.conn.execute(
            "SELECT id, nome FROM empresas WHERE id = ?", (company_id,)).fetchone()

    def add_company(self, nome: str) -> int:
        cur = self.conn.execute("INSERT INTO empresas (nome) VALUES (?)", (nome.strip(),))
        self.conn.commit()
        return cur.lastrowid

    def rename_company(self, company_id: int, nome: str):
        self.conn.execute("UPDATE empresas SET nome = ? WHERE id = ?", (nome.strip(), company_id))
        self.conn.commit()

    def delete_company(self, company_id: int):
        # ON DELETE CASCADE remove também ativos e credenciais da empresa
        self.conn.execute("DELETE FROM empresas WHERE id = ?", (company_id,))
        self.conn.commit()

    # ---- ativos -------------------------------------------------------------
    def list_assets(self, company_id: int):
        return self.conn.execute(
            "SELECT * FROM ativos WHERE empresa_id = ? ORDER BY hostname COLLATE NOCASE",
            (company_id,)).fetchall()

    def get_asset(self, asset_id: int):
        return self.conn.execute("SELECT * FROM ativos WHERE id = ?", (asset_id,)).fetchone()

    def add_asset(self, company_id: int, data: dict) -> int:
        cols = ", ".join(ASSET_FIELDS)
        marks = ", ".join("?" for _ in ASSET_FIELDS)
        cur = self.conn.execute(
            f"INSERT INTO ativos (empresa_id, {cols}) VALUES (?, {marks})",
            (company_id, *[data[f].strip() for f in ASSET_FIELDS]))
        self.conn.commit()
        return cur.lastrowid

    def update_asset(self, asset_id: int, data: dict):
        sets = ", ".join(f"{f} = ?" for f in ASSET_FIELDS)
        self.conn.execute(
            f"UPDATE ativos SET {sets} WHERE id = ?",
            (*[data[f].strip() for f in ASSET_FIELDS], asset_id))
        self.conn.commit()

    def delete_asset(self, asset_id: int):
        self.conn.execute("DELETE FROM ativos WHERE id = ?", (asset_id,))
        self.conn.commit()

    # ---- credenciais (e-mails e senhas) ---------------------------------------
    def list_credentials(self, company_id: int):
        return self.conn.execute(
            "SELECT * FROM credenciais WHERE empresa_id = ? "
            "ORDER BY servico COLLATE NOCASE, email COLLATE NOCASE",
            (company_id,)).fetchall()

    def get_credential(self, cred_id: int):
        return self.conn.execute("SELECT * FROM credenciais WHERE id = ?", (cred_id,)).fetchone()

    def add_credential(self, company_id: int, data: dict) -> int:
        cur = self.conn.execute(
            "INSERT INTO credenciais (empresa_id, servico, email, login, senha_enc, obs) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (company_id, data["servico"].strip(), data["email"].strip(),
             data["login"].strip(), self._seal(data["senha"]), data["obs"].strip()))
        self.conn.commit()
        return cur.lastrowid

    def update_credential(self, cred_id: int, data: dict):
        self.conn.execute(
            "UPDATE credenciais SET servico = ?, email = ?, login = ?, senha_enc = ?, obs = ? "
            "WHERE id = ?",
            (data["servico"].strip(), data["email"].strip(), data["login"].strip(),
             self._seal(data["senha"]), data["obs"].strip(), cred_id))
        self.conn.commit()

    def delete_credential(self, cred_id: int):
        self.conn.execute("DELETE FROM credenciais WHERE id = ?", (cred_id,))
        self.conn.commit()

    # ---- pesquisa global -------------------------------------------------------
    def search_assets(self, term: str, limit: int = 50):
        """Busca por hostname, IP, AnyDesk, função ou SO em todas as empresas."""
        like = _like(term)
        return self.conn.execute(
            """
            SELECT a.*, e.nome AS empresa_nome
              FROM ativos a JOIN empresas e ON e.id = a.empresa_id
             WHERE a.hostname  LIKE ? ESCAPE '\\'
                OR a.ip        LIKE ? ESCAPE '\\'
                OR a.anydesk   LIKE ? ESCAPE '\\'
                OR a.funcao    LIKE ? ESCAPE '\\'
                OR a.modelo_so LIKE ? ESCAPE '\\'
             ORDER BY e.nome COLLATE NOCASE, a.hostname COLLATE NOCASE
             LIMIT ?
            """,
            (like, like, like, like, like, limit)).fetchall()

    def search_credentials(self, term: str, limit: int = 50):
        """Busca por e-mail, login ou serviço (nunca pela senha)."""
        like = _like(term)
        return self.conn.execute(
            """
            SELECT c.*, e.nome AS empresa_nome
              FROM credenciais c JOIN empresas e ON e.id = c.empresa_id
             WHERE c.email   LIKE ? ESCAPE '\\'
                OR c.login   LIKE ? ESCAPE '\\'
                OR c.servico LIKE ? ESCAPE '\\'
             ORDER BY e.nome COLLATE NOCASE, c.email COLLATE NOCASE
             LIMIT ?
            """,
            (like, like, like, limit)).fetchall()

    # ---- histórico para o autocompletar -------------------------------------------
    def history_values(self, table: str, column: str):
        """Valores já digitados antes (mais usados primeiro), sem repetir maiúsc./minúsc."""
        if (table, column) not in _HISTORY_SOURCES:
            raise ValueError("Fonte de histórico não permitida.")
        rows = self.conn.execute(
            f"SELECT {column} AS v FROM {table} WHERE TRIM({column}) <> '' "
            f"GROUP BY {column} COLLATE NOCASE "
            f"ORDER BY COUNT(*) DESC, {column} COLLATE NOCASE").fetchall()
        return [r["v"] for r in rows]

    def email_domains(self, company_id: int):
        """Domínios de e-mail já usados (os da empresa atual primeiro)."""
        rows = self.conn.execute(
            """SELECT LOWER(SUBSTR(email, INSTR(email, '@') + 1)) AS d,
                      SUM(empresa_id = ?) AS aqui, COUNT(*) AS total
                 FROM credenciais WHERE INSTR(email, '@') > 0
                GROUP BY d HAVING d <> ''
                ORDER BY aqui DESC, total DESC, d""", (company_id,)).fetchall()
        return [r["d"] for r in rows]

    # ---- Base de Conhecimento: blocos e manuais -----------------------------------
    _MANUAL_SELECT = """SELECT m.id, m.bloco_id, m.titulo, m.caminho, m.conteudo,
               datetime(m.atualizado_em, 'localtime') AS atualizado_em, b.nome AS bloco_nome
          FROM manuais m JOIN manual_blocos b ON b.id = m.bloco_id"""

    def list_blocks(self):
        return self.conn.execute(
            "SELECT id, nome, ordem FROM manual_blocos ORDER BY ordem, nome COLLATE NOCASE"
        ).fetchall()

    def list_blocks_with_counts(self):
        return self.conn.execute(
            """SELECT b.id, b.nome,
                      (SELECT COUNT(*) FROM manuais m WHERE m.bloco_id = b.id) AS manuais
                 FROM manual_blocos b ORDER BY b.ordem, b.nome COLLATE NOCASE""").fetchall()

    def get_block(self, block_id: int):
        return self.conn.execute(
            "SELECT id, nome, ordem FROM manual_blocos WHERE id = ?", (block_id,)).fetchone()

    def add_block(self, nome: str) -> int:
        cur = self.conn.execute(
            "INSERT INTO manual_blocos (nome, ordem) "
            "VALUES (?, (SELECT COALESCE(MAX(ordem), 0) + 1 FROM manual_blocos))", (nome.strip(),))
        self.conn.commit()
        return cur.lastrowid

    def rename_block(self, block_id: int, nome: str):
        self.conn.execute("UPDATE manual_blocos SET nome = ? WHERE id = ?", (nome.strip(), block_id))
        self.conn.commit()

    def delete_block(self, block_id: int):
        # ON DELETE CASCADE remove também todos os manuais do bloco
        self.conn.execute("DELETE FROM manual_blocos WHERE id = ?", (block_id,))
        self.conn.commit()

    def move_block(self, block_id: int, delta: int):
        """Sobe (-1) ou desce (+1) um bloco na ordem de exibição."""
        ids = [r["id"] for r in self.list_blocks()]
        if block_id not in ids:
            return
        i = ids.index(block_id)
        j = i + delta
        if 0 <= j < len(ids):
            ids[i], ids[j] = ids[j], ids[i]
        with self.conn:
            for pos, bid in enumerate(ids, start=1):
                self.conn.execute("UPDATE manual_blocos SET ordem = ? WHERE id = ?", (pos, bid))

    def list_manuals(self):
        return self.conn.execute(
            self._MANUAL_SELECT + " ORDER BY b.ordem, b.nome COLLATE NOCASE, "
                                  "m.titulo COLLATE NOCASE").fetchall()

    def get_manual(self, manual_id: int):
        return self.conn.execute(self._MANUAL_SELECT + " WHERE m.id = ?", (manual_id,)).fetchone()

    def add_manual(self, block_id: int, titulo: str, caminho: str, conteudo: str) -> int:
        cur = self.conn.execute(
            "INSERT INTO manuais (bloco_id, titulo, caminho, conteudo) VALUES (?, ?, ?, ?)",
            (block_id, titulo.strip(), caminho.strip(), conteudo.strip()))
        self.conn.commit()
        return cur.lastrowid

    def update_manual(self, manual_id: int, block_id: int, titulo: str, caminho: str, conteudo: str):
        self.conn.execute(
            "UPDATE manuais SET bloco_id = ?, titulo = ?, caminho = ?, conteudo = ?, "
            "atualizado_em = CURRENT_TIMESTAMP WHERE id = ?",
            (block_id, titulo.strip(), caminho.strip(), conteudo.strip(), manual_id))
        self.conn.commit()

    def delete_manual(self, manual_id: int):
        self.conn.execute("DELETE FROM manuais WHERE id = ?", (manual_id,))
        self.conn.commit()

    def search_manuals(self, term: str, limit: int = 50):
        """Busca em título, conteúdo, caminho e nome do bloco (título primeiro)."""
        like = _like(term)
        return self.conn.execute(
            self._MANUAL_SELECT + """
             WHERE m.titulo   LIKE ? ESCAPE '\\' OR m.conteudo LIKE ? ESCAPE '\\'
                OR m.caminho  LIKE ? ESCAPE '\\' OR b.nome     LIKE ? ESCAPE '\\'
             ORDER BY (m.titulo LIKE ? ESCAPE '\\') DESC, b.ordem,
                      b.nome COLLATE NOCASE, m.titulo COLLATE NOCASE
             LIMIT ?""", (like, like, like, like, like, limit)).fetchall()

    def search_blocks(self, term: str, limit: int = 20):
        return self.conn.execute(
            "SELECT id, nome FROM manual_blocos WHERE nome LIKE ? ESCAPE '\\' "
            "ORDER BY ordem, nome COLLATE NOCASE LIMIT ?", (_like(term), limit)).fetchall()


# --------------------------------------------------------------------------
# Funções puras de apoio (autocompletar, validação, exibição)
# --------------------------------------------------------------------------
DEFAULT_SUGGESTIONS = {
    "funcao": ["Servidor de Active Directory", "Servidor de Arquivos",
               "Servidor de Banco de Dados", "Servidor ERP", "Servidor de Aplicação",
               "Servidor de Backup", "Servidor de Impressão", "Servidor Web",
               "Hypervisor (Hyper-V)", "Hypervisor (VMware)", "Firewall", "Estação"],
    "modelo_so": ["Windows Server 2012 R2", "Windows Server 2016", "Windows Server 2019",
                  "Windows Server 2022", "Windows 10", "Windows 11",
                  "Ubuntu Server 22.04", "Debian 12"],
    "wireguard": ["Sim", "Não", "Pendente"],
    "openvpn": ["Sim", "Não", "Pendente"],
    "servico": ["Microsoft 365", "Google Workspace", "Zimbra", "E-mail IMAP/SMTP", "Webmail"],
}


def merge_unique(*lists):
    """Junta listas sem repetir (ignora maiúsc./minúsc.), mantendo a ordem."""
    seen, out = set(), []
    for items in lists:
        for item in items:
            key = item.strip().casefold()
            if key and key not in seen:
                seen.add(key)
                out.append(item.strip())
    return out


def rank_suggestions(candidates, text, limit=8):
    """Sugestões que COMEÇAM com o texto vêm primeiro; depois as que o CONTÊM."""
    needle = text.strip().casefold()
    if not needle:
        return list(candidates)[:limit]
    starts, contains = [], []
    for cand in candidates:
        low = cand.casefold()
        if low.startswith(needle):
            starts.append(cand)
        elif needle in low:
            contains.append(cand)
    return (starts + contains)[:limit]


def email_suggestions(domains, text, limit=8):
    """Depois do '@', sugere os domínios já usados: 'joao@' -> 'joao@empresa.com.br'."""
    local, at, partial = text.partition("@")
    if not at or not local.strip():
        return []
    partial = partial.strip().casefold()
    return [f"{local}@{d}" for d in domains if d.casefold().startswith(partial)][:limit]


def validate_ips(text: str):
    """Aceita um ou mais IPs separados por vírgula/;/espaço. Retorna o IP inválido ou None."""
    for token in re.split(r"[,\s;]+", text.strip()):
        if not token:
            continue
        try:
            ipaddress.ip_address(token)
        except ValueError:
            return token
    return None


def status_display(text: str) -> str:
    """Realça Sim/Não na tabela (o valor copiado continua sendo o original)."""
    value = (text or "").strip()
    low = value.casefold()
    if low == "sim":
        return "✔ Sim"
    if low in ("não", "nao"):
        return "✘ Não"
    return value


# Arquivos que o botão "Abrir" NUNCA executa (o banco pode ser editado por terceiros).
_BLOCKED_EXTENSIONS = {
    ".exe", ".bat", ".cmd", ".com", ".msi", ".msp", ".scr", ".ps1", ".psm1", ".vbs", ".vbe",
    ".js", ".jse", ".wsf", ".wsh", ".hta", ".lnk", ".reg", ".jar", ".cpl", ".dll", ".sh",
    ".py", ".pyw",
}


def open_path(target: str):
    """Abre arquivo/pasta/link com o programa padrão. Retorna mensagem de erro ou None."""
    target = (target or "").strip().strip('"').strip()
    if not target:
        return "Este manual não tem caminho ou link."
    if re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*://", target):
        if not re.match(r"^https?://", target, re.I):
            return "Por segurança, só links http:// e https:// podem ser abertos."
        return None if webbrowser.open(target) else "Não foi possível abrir o navegador."
    path = os.path.expandvars(os.path.expanduser(target))
    ext = os.path.splitext(path)[1].lower()
    if ext in _BLOCKED_EXTENSIONS:
        return (f"Por segurança, o programa não abre executáveis/scripts ({ext}).\n"
                "Use «Copiar caminho» e abra pelo Explorador de Arquivos.")
    if not os.path.exists(path):
        return (f"Caminho não encontrado:\n{path}\n\n"
                "Confira o caminho e se a rede/VPN está conectada.")
    try:
        if sys.platform == "win32":
            os.startfile(path)                       # noqa: S606 (extensão já filtrada acima)
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
    except OSError as exc:
        return f"Não foi possível abrir:\n{exc}"
    return None


def manual_kind(manual) -> str:
    """'Link', 'Arquivo' ou 'Procedimento' (só texto)."""
    path = (manual["caminho"] or "").strip()
    if re.match(r"^https?://", path, re.I):
        return "Link"
    return "Arquivo" if path else "Procedimento"


def short_path(text: str, limit: int = 60) -> str:
    """Encurta caminhos longos no meio: \\\\servidor\\pasta\u2026\\arquivo.pdf"""
    if len(text) <= limit:
        return text
    head = limit // 3
    return text[:head] + "…" + text[-(limit - head - 1):]


# --------------------------------------------------------------------------
# Visual
# --------------------------------------------------------------------------
FONT = "Segoe UI"
FONT_BASE = (FONT, 11)
FONT_BOLD = (FONT, 11, "bold")

COLORS = {
    "bg": "#F1F5F9",          # fundo geral
    "surface": "#FFFFFF",     # cartões / tabelas
    "text": "#0F172A",
    "muted": "#475569",
    "border": "#CBD5E1",
    "head": "#E2E8F0",
    "row_alt": "#F8FAFC",
    "side": "#0F172A",        # menu lateral
    "side_hover": "#1E293B",
    "side_hover2": "#334155",
    "side_sel": "#2563EB",
    "side_fg": "#F8FAFC",
    "side_muted": "#94A3B8",
    "primary": "#1D4ED8",
    "primary_hover": "#1E40AF",
    "success": "#15803D",
    "success_hover": "#166534",
    "danger": "#B91C1C",
    "danger_hover": "#991B1B",
    "danger_soft": "#FEE2E2",
    "warn": "#B45309",
    "toast": "#0F172A",
}

FIELD_LABELS = {
    "hostname": "Hostname", "ip": "IP", "wireguard": "WireGuard", "openvpn": "OpenVPN",
    "anydesk": "AnyDesk", "funcao": "Função", "estrutura": "Estrutura",
    "modelo_so": "Modelo/SO", "servico": "Serviço", "email": "E-mail",
    "login": "Login", "senha": "Senha", "obs": "Observações",
    "bloco": "Bloco", "titulo": "Título", "caminho": "Caminho", "conteudo": "Conteúdo",
    "nome": "Nome",
}

TREE_COLUMNS = [
    ("hostname", "HOSTNAME", 150),
    ("ip", "IP", 130),
    ("wireguard", "WIREGUARD", 100),
    ("openvpn", "OPENVPN", 100),
    ("anydesk", "ANYDESK", 120),
    ("funcao", "FUNÇÃO", 210),
    ("estrutura", "ESTRUTURA", 100),
    ("modelo_so", "MODELO/SO", 200),
]
CRED_COLUMNS = [
    ("servico", "SERVIÇO", 150),
    ("email", "E-MAIL", 270),
    ("login", "LOGIN", 210),
    ("senha", "SENHA", 150),
    ("obs", "OBSERVAÇÕES", 260),
]
STRUCTURE_OPTIONS = ["Físico", "Virtual", "Híbrido"]

ASSET_FORM_FIELDS = [
    {"key": "hostname", "required": True},
    {"key": "ip"},
    {"key": "wireguard", "kind": "auto"},
    {"key": "openvpn", "kind": "auto"},
    {"key": "anydesk"},
    {"key": "funcao", "kind": "auto"},
    {"key": "estrutura", "kind": "choice", "choices": STRUCTURE_OPTIONS},
    {"key": "modelo_so", "kind": "auto"},
]
CRED_FORM_FIELDS = [
    {"key": "servico", "kind": "auto"},
    {"key": "email", "kind": "auto", "required": True},
    {"key": "login", "label": "Login (vazio = igual ao e-mail)"},
    {"key": "senha", "kind": "password"},
    {"key": "obs"},
]


def make_card(parent, title=None, subtitle=None):
    """Cartão branco com borda fina. Retorna (cartão, corpo)."""
    card = tk.Frame(parent, bg=COLORS["surface"], highlightbackground=COLORS["border"],
                    highlightthickness=1)
    body = ttk.Frame(card, style="Card.TFrame", padding=20)
    body.pack(fill="both", expand=True)
    if title:
        ttk.Label(body, text=title, style="Section.TLabel").pack(anchor="w")
    if subtitle:
        ttk.Label(body, text=subtitle, style="CardMuted.TLabel", wraplength=820,
                  justify="left").pack(anchor="w", pady=(2, 0))
    return card, body


class ScrollFrame(tk.Frame):
    """
    Área rolável (Canvas + Scrollbar + Frame interno `.inner`) com rolagem pela roda do
    mouse. Usada na lista de empresas e na tela de manuais.
    `on_width(largura)` é chamado quando a largura muda (para reorganizar cartões).
    """

    def __init__(self, parent, bg):
        super().__init__(parent, bg=bg)
        self.on_width = None
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.vsb.grid(row=0, column=1, sticky="ns")
        self.inner = tk.Frame(self.canvas, bg=bg)
        self._window = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.inner.bind("<Configure>",
                        lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", self._on_canvas_configure)
        self.canvas.bind("<Enter>", self._bind_wheel)
        self.canvas.bind("<Leave>", self._unbind_wheel)
        self.inner.bind("<Enter>", self._bind_wheel)

    def _on_canvas_configure(self, event):
        self.canvas.itemconfigure(self._window, width=event.width)
        if self.on_width:
            self.on_width(event.width)

    def _bind_wheel(self, _event=None):
        self.bind_all("<MouseWheel>", self._on_wheel)
        self.bind_all("<Button-4>", self._on_wheel)    # Linux
        self.bind_all("<Button-5>", self._on_wheel)

    def _unbind_wheel(self, _event=None):
        # só desliga se o ponteiro realmente saiu da área rolável
        try:
            x, y = self.winfo_pointerxy()
            w = self.winfo_containing(x, y)
        except (KeyError, tk.TclError):
            w = None
        while w is not None:
            if w is self.canvas:
                return
            w = getattr(w, "master", None)
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.unbind_all(seq)

    def _on_wheel(self, event):
        try:
            if self.canvas.yview() == (0.0, 1.0):
                return   # nada para rolar
            if event.num == 4:
                step = -1
            elif event.num == 5:
                step = 1
            else:
                step = -1 if event.delta > 0 else 1
            self.canvas.yview_scroll(step, "units")
        except tk.TclError:
            pass


# --------------------------------------------------------------------------
# Widget: campo de texto com sugestões (histórico) estilo "intellisense"
# --------------------------------------------------------------------------
class AutocompleteEntry(ttk.Entry):
    """
    Campo de texto que mostra uma lista de sugestões enquanto você digita.

    - A lista vem de `provider(texto) -> [sugestões]` (histórico do banco).
    - Seta ↓/↑ navega; Enter ou clique aceita a sugestão destacada;
      Tab aceita a destacada (ou a primeira, se ela começar com o que foi
      digitado) e vai para o próximo campo; Esc fecha a lista.
    - A lista é um Listbox "colocado" dentro da própria janela (sem criar
      outra janela), por isso nunca rouba o foco do campo.
    """
    _IGNORED_KEYS = {
        "Up", "Down", "Left", "Right", "Return", "KP_Enter", "Tab", "ISO_Left_Tab",
        "Escape", "Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R",
        "Caps_Lock", "Home", "End", "Prior", "Next", "Menu",
    }

    def __init__(self, master, variable, provider, **kwargs):
        super().__init__(master, textvariable=variable, **kwargs)
        self._var = variable
        self._provider = provider
        self._listbox = None
        self._items = []
        self.bind("<KeyRelease>", self._on_key_release, add="+")
        self.bind("<Down>", self._on_down)
        self.bind("<Up>", self._on_up)
        self.bind("<Return>", self._on_return)
        self.bind("<Tab>", self._on_tab)
        self.bind("<Escape>", self._on_escape)
        self.bind("<FocusOut>", self._on_focus_out, add="+")

    # -- lista -----------------------------------------------------------------
    def _visible(self) -> bool:
        return self._listbox is not None and bool(self._listbox.winfo_ismapped())

    def _ensure_listbox(self):
        if self._listbox is None:
            self._listbox = tk.Listbox(
                self.winfo_toplevel(), font=FONT_BASE, activestyle="none",
                exportselection=False, relief="solid", bd=1, highlightthickness=0,
                selectbackground=COLORS["primary"], selectforeground="white",
                bg="white", fg=COLORS["text"])
            self._listbox.bind("<ButtonRelease-1>", self._on_click)
        return self._listbox

    def _suggestions(self, text):
        try:
            return [s for s in self._provider(text) if s != text]
        except Exception:      # um erro no provedor nunca deve travar a digitação
            return []

    def _show(self, items):
        lb = self._ensure_listbox()
        self._items = list(items)
        lb.delete(0, "end")
        for item in self._items:
            lb.insert("end", item)
        lb.configure(height=min(len(self._items), 6))
        lb.place(in_=self, relx=0.0, rely=1.0, relwidth=1.0, y=1)
        lb.lift()

    def _hide(self):
        if self._listbox is not None:
            try:
                self._listbox.place_forget()
            except tk.TclError:
                pass
        self._items = []

    def _current_index(self):
        sel = self._listbox.curselection() if self._listbox is not None else ()
        return sel[0] if sel else None

    def _move(self, delta):
        count = len(self._items)
        if not count:
            return
        idx = self._current_index()
        new = 0 if idx is None and delta > 0 else count - 1 if idx is None else \
            max(0, min(count - 1, idx + delta))
        self._listbox.selection_clear(0, "end")
        self._listbox.selection_set(new)
        self._listbox.activate(new)
        self._listbox.see(new)

    def _accept(self, index):
        if 0 <= index < len(self._items):
            self._var.set(self._items[index])
            self.icursor("end")
        self._hide()

    # -- eventos -----------------------------------------------------------------
    def _on_key_release(self, event):
        if event.keysym in self._IGNORED_KEYS:
            return
        text = self._var.get()
        items = self._suggestions(text) if text.strip() else []
        if items:
            self._show(items)
        else:
            self._hide()

    def _on_down(self, _event):
        if self._visible():
            self._move(1)
        else:
            items = self._suggestions(self._var.get())
            if items:
                self._show(items)
        return "break"

    def _on_up(self, _event):
        if self._visible():
            self._move(-1)
            return "break"
        return None

    def _on_return(self, _event):
        if self._visible():
            idx = self._current_index()
            if idx is not None:
                self._accept(idx)
                return "break"      # só aceitou a sugestão; não salva o formulário
            self._hide()
        return None                  # segue: o formulário trata o Enter

    def _on_tab(self, _event):
        if self._visible() and self._items:
            idx = self._current_index()
            if idx is None and self._items[0].casefold().startswith(self._var.get().strip().casefold()):
                idx = 0
            if idx is not None:
                self._accept(idx)
            else:
                self._hide()
        return None                  # o Tab continua e move o foco

    def _on_escape(self, _event):
        if self._visible():
            self._hide()
            return "break"
        return None

    def _on_click(self, event):
        idx = self._listbox.nearest(event.y)
        self._accept(idx)
        self.focus_set()

    def _on_focus_out(self, _event):
        self.after(150, self._check_focus)

    def _check_focus(self):
        try:
            if not self.winfo_exists():
                return
            current = self.focus_get()
        except (tk.TclError, KeyError):
            current = None
        if current is not self and current is not self._listbox:
            self._hide()


# --------------------------------------------------------------------------
# Janela de formulário genérica (usada em todos os cadastros)
# --------------------------------------------------------------------------
class FormDialog(tk.Toplevel):
    """
    Formulário modal. `fields` é uma lista de dicts:
      key, label (opcional), required, kind =
        "entry"    texto simples
        "auto"     texto com sugestões do histórico (usa suggest[key])
        "choice"   lista fixa (choices)
        "password" senha com 'Mostrar' e 'Gerar'
        "secret"   senha mascarada (sem extras)
        "text"     texto de várias linhas (Enter = nova linha)
        "path"     caminho de arquivo com botão 'Procurar...' 
    `validate(dados) -> mensagem_de_erro | None` roda antes de fechar.
    O resultado fica em self.result (dict) ou None se cancelado.
    """

    def __init__(self, parent, title, fields, initial=None, suggest=None, validate=None,
                 intro=None, save_text="Salvar", save_style="Primary.TButton"):
        super().__init__(parent)
        self.configure(bg=COLORS["surface"])
        self.title(title)
        self.resizable(False, False)
        self.transient(parent)
        self.result = None
        self._fields = fields
        self._validate = validate
        self.vars = {}
        self.texts = {}      # campos de várias linhas (tk.Text)
        initial = initial or {}
        suggest = suggest or {}

        body = ttk.Frame(self, style="Card.TFrame", padding=26)
        body.pack(fill="both", expand=True)
        row = 0
        if intro:
            ttk.Label(body, text=intro, style="CardMuted.TLabel", wraplength=470,
                      justify="left").grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 14))
            row = 1

        first = None
        for field in fields:
            key = field["key"]
            kind = field.get("kind", "entry")
            label = field.get("label") or FIELD_LABELS.get(key, key)
            if field.get("required"):
                label += " *"
            ttk.Label(body, text=label, style="Card.TLabel").grid(
                row=row, column=0, sticky="nw" if kind == "text" else "w", pady=7,
                padx=(0, 16))
            var = tk.StringVar(value=initial.get(key, "") or "")
            self.vars[key] = var

            container = None
            if kind == "choice":
                widget = ttk.Combobox(body, textvariable=var, values=field["choices"],
                                      state="readonly", width=36, font=FONT_BASE)
            elif kind == "auto":
                widget = AutocompleteEntry(body, var, suggest.get(key, lambda t: []),
                                           width=38, font=FONT_BASE)
            elif kind in ("password", "secret"):
                widget = ttk.Entry(body, textvariable=var, show="•", width=38, font=FONT_BASE)
            elif kind == "text":
                container = ttk.Frame(body, style="Card.TFrame")
                widget = tk.Text(container, width=44, height=9, wrap="word", font=FONT_BASE,
                                 relief="solid", bd=1, padx=8, pady=6, highlightthickness=0,
                                 undo=True)
                text_sb = ttk.Scrollbar(container, orient="vertical", command=widget.yview)
                widget.configure(yscrollcommand=text_sb.set)
                widget.pack(side="left", fill="both", expand=True)
                text_sb.pack(side="left", fill="y")
                widget.insert("1.0", initial.get(key, "") or "")
                # Tab sai do campo (em vez de inserir tabulação)
                widget.bind("<Tab>", lambda e: (e.widget.tk_focusNext().focus_set(), "break")[1])
                self.texts[key] = widget
            else:
                widget = ttk.Entry(body, textvariable=var, width=38, font=FONT_BASE)
            target = container if container is not None else widget
            target.grid(row=row, column=1, sticky="ew", pady=7)
            if kind == "password":
                self._add_password_tools(body, row, widget, var)
            elif kind == "path":
                self._add_browse_button(body, row, var)
            if first is None:
                first = widget
            row += 1

        buttons = ttk.Frame(body, style="Card.TFrame")
        buttons.grid(row=row, column=0, columnspan=3, sticky="e", pady=(18, 0))
        ttk.Button(buttons, text="Cancelar", style="Tool.TButton",
                   command=self.destroy).pack(side="right", padx=(10, 0))
        ttk.Button(buttons, text=save_text, style=save_style,
                   command=self._save).pack(side="right")

        self.bind("<Return>", self._on_return)
        self.bind("<KP_Enter>", self._on_return)
        self.bind("<Escape>", lambda e: self.destroy())

        self.update_idletasks()
        top = parent.winfo_toplevel()
        x = top.winfo_rootx() + (top.winfo_width() - self.winfo_width()) // 2
        y = top.winfo_rooty() + (top.winfo_height() - self.winfo_height()) // 3
        self.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        try:
            self.wait_visibility()
            self.grab_set()
        except tk.TclError:
            pass
        if first is not None:
            first.focus_set()

    def _add_password_tools(self, body, row, entry, var):
        tools = ttk.Frame(body, style="Card.TFrame")
        tools.grid(row=row, column=2, sticky="w", padx=(10, 0))
        show = tk.BooleanVar(value=False)

        def toggle():
            entry.configure(show="" if show.get() else "•")

        def generate():
            var.set(generate_password())
            show.set(True)
            toggle()

        ttk.Checkbutton(tools, text="Mostrar", variable=show, command=toggle,
                        style="Card.TCheckbutton").pack(side="left")
        ttk.Button(tools, text="Gerar", style="Tool.TButton", command=generate).pack(
            side="left", padx=(8, 0))

    def _add_browse_button(self, body, row, var):
        def browse():
            chosen = filedialog.askopenfilename(parent=self, title="Selecionar arquivo do manual")
            if chosen:
                var.set(os.path.normpath(chosen))

        ttk.Button(body, text="Procurar...", style="Tool.TButton", command=browse).grid(
            row=row, column=2, sticky="w", padx=(10, 0))

    def _on_return(self, _event):
        focused = self.focus_get()
        if isinstance(focused, tk.Text):         # Enter em campo de texto = nova linha
            return None
        if isinstance(focused, ttk.Button):      # Enter em um botão aciona o botão
            focused.invoke()
        else:
            self._save()
        return "break"

    def _save(self):
        data = {}
        for field in self._fields:
            if field["key"] in self.texts:
                value = self.texts[field["key"]].get("1.0", "end-1c")
            else:
                value = self.vars[field["key"]].get()
            if field.get("kind") not in ("password", "secret"):
                value = value.strip()
            data[field["key"]] = value
        for field in self._fields:
            if field.get("required") and not data[field["key"]]:
                label = field.get("label") or FIELD_LABELS.get(field["key"], field["key"])
                messagebox.showwarning("Campo obrigatório", f"Preencha o campo: {label}.",
                                       parent=self)
                return
        if self._validate is not None:
            error = self._validate(data)
            if error:
                messagebox.showwarning("Verifique os dados", error, parent=self)
                return
        self.result = data
        self.destroy()


def ask_form(parent, title, fields, **kwargs):
    """Abre o formulário, espera fechar e devolve o dict (ou None)."""
    dialog = FormDialog(parent, title, fields, **kwargs)
    parent.wait_window(dialog)
    return dialog.result


# --------------------------------------------------------------------------
# Painel de tabela com CRUD + copiar com um clique (base das duas abas)
# --------------------------------------------------------------------------
class TablePanel(ttk.Frame):
    columns = ()
    copy_fields = ()           # [(chave, rótulo)] -> botões "Copiar" e menu de contexto
    add_text = "+ Adicionar"
    noun_plural = "itens"
    sensitive_keys = ()        # colunas cujo conteúdo não aparece no aviso de cópia

    def __init__(self, parent, app):
        super().__init__(parent, style="Surface.TFrame", padding=(18, 16))
        self.app = app
        self.db = app.db
        self.company_id = None
        self.on_change = None
        self._rows = {}
        self._last_key = None
        self.columnconfigure(0, weight=1)
        self.rowconfigure(2, weight=1)
        self._build_toolbar()
        self._build_copybar()
        self._build_table()
        self._build_footer()

    # ---- construção -----------------------------------------------------------
    def _build_toolbar(self):
        bar = ttk.Frame(self, style="Surface.TFrame")
        bar.grid(row=0, column=0, sticky="ew")
        ttk.Button(bar, text=self.add_text, style="Primary.TButton",
                   command=self.add).pack(side="left")
        ttk.Button(bar, text="Editar", style="Tool.TButton",
                   command=self.edit).pack(side="left", padx=8)
        ttk.Button(bar, text="Remover", style="DangerSoft.TButton",
                   command=self.remove).pack(side="left")
        extra = ttk.Frame(bar, style="Surface.TFrame")
        extra.pack(side="right")
        self.build_extra_toolbar(extra)

    def build_extra_toolbar(self, frame):
        """Gancho para as subclasses acrescentarem controles à direita da barra."""

    def _build_copybar(self):
        bar = ttk.Frame(self, style="Surface.TFrame")
        bar.grid(row=1, column=0, sticky="ew", pady=(12, 0))
        ttk.Label(bar, text="Copiar da linha selecionada:", style="CardMuted.TLabel").pack(side="left")
        for key, label in self.copy_fields:
            ttk.Button(bar, text=label, style="Copy.TButton",
                       command=lambda k=key: self._copy_selected(k)).pack(side="left", padx=(8, 0))

    def _build_table(self):
        box = ttk.Frame(self, style="Surface.TFrame")
        box.grid(row=2, column=0, sticky="nsew", pady=(10, 0))
        box.rowconfigure(0, weight=1)
        box.columnconfigure(0, weight=1)
        keys = [c[0] for c in self.columns]
        self.tree = ttk.Treeview(box, columns=keys, show="headings", selectmode="browse")
        for key, title, width in self.columns:
            self.tree.heading(key, text=title, anchor="w",
                              command=lambda k=key: self._sort(k, False))
            self.tree.column(key, width=width, minwidth=70, anchor="w")
        vsb = ttk.Scrollbar(box, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(box, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        self.tree.tag_configure("odd", background=COLORS["row_alt"])
        self.tree.tag_configure("even", background=COLORS["surface"])

        self.tree.bind("<ButtonPress-1>", self._remember_column, add="+")
        self.tree.bind("<Double-1>", self._on_double_click)
        self.tree.bind("<Button-3>", self._on_right_click)
        if sys.platform == "darwin":
            self.tree.bind("<Button-2>", self._on_right_click)
            self.tree.bind("<Control-Button-1>", self._on_right_click)
        self.tree.bind("<Return>", lambda e: self.edit())
        self.tree.bind("<Delete>", lambda e: self.remove())
        self.tree.bind("<Control-c>", self._on_ctrl_c)

    def _build_footer(self):
        footer = ttk.Frame(self, style="Surface.TFrame")
        footer.grid(row=3, column=0, sticky="ew", pady=(10, 0))
        self.count_var = tk.StringVar(value="")
        ttk.Label(footer, textvariable=self.count_var, style="CardMuted.TLabel").pack(side="left")
        ttk.Label(footer, style="CardMuted.TLabel",
                  text="Duplo clique em uma célula = copiar  •  Clique direito = mais opções  •  "
                       "Enter = editar").pack(side="right")

    # ---- dados ------------------------------------------------------------------
    def set_company(self, company_id):
        self.company_id = company_id
        self.refresh()

    def refresh(self, select_id=None):
        self.tree.delete(*self.tree.get_children())
        self._rows = {}
        if self.company_id is None:
            self.count_var.set("")
            return
        rows = self.list_rows()
        for i, row in enumerate(rows):
            self._rows[row["id"]] = row
            self.tree.insert("", "end", iid=str(row["id"]), values=self.display_values(row),
                             tags=("odd" if i % 2 else "even",))
        self.count_var.set(f"{len(rows)} {self.noun_plural}")
        if select_id is not None and self.tree.exists(str(select_id)):
            self.tree.selection_set(str(select_id))
            self.tree.focus(str(select_id))
            self.tree.see(str(select_id))
        if self.on_change:
            self.on_change()

    def _sort(self, col, reverse):
        items = [(self.tree.set(i, col).casefold(), i) for i in self.tree.get_children("")]
        items.sort(reverse=reverse)
        for idx, (_, iid) in enumerate(items):
            self.tree.move(iid, "", idx)
            self.tree.item(iid, tags=("odd" if idx % 2 else "even",))
        self.tree.heading(col, command=lambda: self._sort(col, not reverse))

    def selected_id(self):
        sel = self.tree.selection()
        return int(sel[0]) if sel else None

    def _selected_row(self):
        return self._rows.get(self.selected_id())

    # ---- copiar -------------------------------------------------------------------
    def _column_key(self, event):
        try:
            idx = int(self.tree.identify_column(event.x).replace("#", "")) - 1
        except ValueError:
            return None
        return self.columns[idx][0] if 0 <= idx < len(self.columns) else None

    def _remember_column(self, event):
        key = self._column_key(event)
        if key:
            self._last_key = key

    def _copy_selected(self, key):
        row = self._selected_row()
        if row is None:
            self.app.toast("Selecione uma linha primeiro", "warn")
            return
        text = self.copy_text(row, key)
        if not text:
            self.app.toast(f"{FIELD_LABELS.get(key, key)} está vazio nesta linha", "warn")
            return
        self.app.copy_to_clipboard(text, FIELD_LABELS.get(key, key),
                                   sensitive=key in self.sensitive_keys)

    def _on_double_click(self, event):
        if self.tree.identify_region(event.x, event.y) != "cell":
            return
        iid = self.tree.identify_row(event.y)
        key = self._column_key(event)
        if not iid or not key:
            return
        self.tree.selection_set(iid)
        self._copy_selected(key)

    def _on_ctrl_c(self, _event):
        key = self._last_key or (self.copy_fields[0][0] if self.copy_fields else None)
        if key:
            self._copy_selected(key)
        return "break"

    def _on_right_click(self, event):
        iid = self.tree.identify_row(event.y)
        if not iid:
            return
        self.tree.selection_set(iid)
        self.tree.focus(iid)
        clicked = self._column_key(event)
        menu = tk.Menu(self, tearoff=0, font=FONT_BASE)
        for key, label in self.copy_fields:
            menu.add_command(label=f"Copiar {label}", command=lambda k=key: self._copy_selected(k))
        if clicked and clicked not in [k for k, _ in self.copy_fields]:
            menu.add_command(label=f"Copiar {FIELD_LABELS.get(clicked, clicked)} (célula clicada)",
                             command=lambda k=clicked: self._copy_selected(k))
        menu.add_separator()
        menu.add_command(label="Editar...", command=self.edit)
        menu.add_command(label="Remover...", command=self.remove)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    # ---- CRUD -----------------------------------------------------------------------
    def add(self):
        if self.company_id is None:
            return
        data = self.ask_form(None)
        if data is None:
            return
        try:
            new_id = self.db_add(data)
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicado", self.duplicate_message(data),
                                 parent=self.winfo_toplevel())
            return
        self.refresh(select_id=new_id)
        self.app.toast("✔ Cadastro salvo")

    def edit(self):
        row = self._selected_row()
        if row is None:
            self.app.toast("Selecione uma linha para editar", "warn")
            return
        data = self.ask_form(row)
        if data is None:
            return
        try:
            self.db_update(row["id"], data)
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicado", self.duplicate_message(data),
                                 parent=self.winfo_toplevel())
            return
        self.refresh(select_id=row["id"])
        self.app.toast("✔ Alterações salvas")

    def remove(self):
        row = self._selected_row()
        if row is None:
            self.app.toast("Selecione uma linha para remover", "warn")
            return
        if not messagebox.askyesno("Remover", f"Remover «{self.row_name(row)}»?\n\n"
                                   "Esta ação não pode ser desfeita.", icon="warning",
                                   default="no", parent=self.winfo_toplevel()):
            return
        self.db_delete(row["id"])
        self.refresh()
        self.app.toast("✔ Removido")

    # ---- ganchos das subclasses -------------------------------------------------------
    def list_rows(self):
        raise NotImplementedError

    def display_values(self, row):
        raise NotImplementedError

    def copy_text(self, row, key):
        return (row[key] or "").strip()

    def ask_form(self, row):
        raise NotImplementedError

    def db_add(self, data):
        raise NotImplementedError

    def db_update(self, row_id, data):
        raise NotImplementedError

    def db_delete(self, row_id):
        raise NotImplementedError

    def row_name(self, row):
        raise NotImplementedError

    def duplicate_message(self, data):
        return "Já existe um cadastro igual."


class AssetsPanel(TablePanel):
    """Aba 'Infraestrutura / Servidores'."""
    columns = TREE_COLUMNS
    copy_fields = [("hostname", "Hostname"), ("ip", "IP"), ("anydesk", "AnyDesk")]
    add_text = "+ Adicionar Novo Ativo/Servidor"
    noun_plural = "ativo(s)"

    def list_rows(self):
        return self.db.list_assets(self.company_id)

    def display_values(self, row):
        values = []
        for key, _, _ in self.columns:
            value = row[key] or ""
            if key in ("wireguard", "openvpn"):
                value = status_display(value)
            values.append(value)
        return values

    def ask_form(self, row):
        # Histórico vindo do banco (mais usados primeiro) + sugestões padrão.
        suggest = {}
        for key in ("funcao", "modelo_so", "wireguard", "openvpn"):
            items = merge_unique(self.db.history_values("ativos", key),
                                 DEFAULT_SUGGESTIONS[key])
            suggest[key] = lambda text, items=items: rank_suggestions(items, text)
        title = f"Editar {row['hostname']}" if row else "Novo Ativo/Servidor"
        return ask_form(self.app, title, ASSET_FORM_FIELDS,
                        initial=dict(row) if row else None,
                        suggest=suggest, validate=self._validate)

    @staticmethod
    def _validate(data):
        bad = validate_ips(data["ip"])
        return f"'{bad}' não é um endereço IP válido." if bad else None

    def db_add(self, data):
        return self.db.add_asset(self.company_id, data)

    def db_update(self, row_id, data):
        self.db.update_asset(row_id, data)

    def db_delete(self, row_id):
        self.db.delete_asset(row_id)

    def row_name(self, row):
        return row["hostname"]

    def duplicate_message(self, data):
        return f"Já existe um ativo '{data['hostname']}' nesta empresa."


class CredentialsPanel(TablePanel):
    """Aba 'E-mails e Credenciais'. Senhas ficam criptografadas no banco."""
    columns = CRED_COLUMNS
    copy_fields = [("email", "E-mail"), ("login", "Login"), ("senha", "Senha")]
    add_text = "+ Adicionar E-mail/Credencial"
    noun_plural = "conta(s)"
    sensitive_keys = ("senha",)

    def __init__(self, parent, app):
        self.show_passwords = tk.BooleanVar(value=False)
        super().__init__(parent, app)

    def build_extra_toolbar(self, frame):
        ttk.Checkbutton(frame, text="Mostrar senhas na tabela", variable=self.show_passwords,
                        command=self._toggle_passwords, style="Card.TCheckbutton").pack(side="left")

    def _toggle_passwords(self):
        self.refresh(select_id=self.selected_id())

    def hide_passwords(self):
        """Volta a mascarar as senhas (ao trocar de empresa/aba)."""
        if self.show_passwords.get():
            self.show_passwords.set(False)
            self.refresh(select_id=self.selected_id())

    def set_company(self, company_id):
        self.show_passwords.set(False)
        super().set_company(company_id)

    def list_rows(self):
        return self.db.list_credentials(self.company_id)

    def display_values(self, row):
        values = []
        for key, _, _ in self.columns:
            if key == "senha":
                if not row["senha_enc"]:
                    values.append("")
                elif self.show_passwords.get():
                    try:
                        values.append(self.db.reveal(row["senha_enc"]))
                    except ValueError:
                        values.append("⚠ erro ao decifrar")
                else:
                    values.append("••••••••")
            else:
                values.append(row[key] or "")
        return values

    def copy_text(self, row, key):
        if key == "senha":
            try:
                return self.db.reveal(row["senha_enc"])
            except ValueError:
                messagebox.showerror("Cofre", "Não foi possível decifrar esta senha.",
                                     parent=self.winfo_toplevel())
                return ""
        return (row[key] or "").strip()

    def ask_form(self, row):
        initial = dict(row) if row else {}
        if row:
            try:
                initial["senha"] = self.db.reveal(row["senha_enc"])
            except ValueError:
                messagebox.showerror("Cofre", "Não foi possível decifrar a senha atual.",
                                     parent=self.winfo_toplevel())
                return None
        services = merge_unique(self.db.history_values("credenciais", "servico"),
                                DEFAULT_SUGGESTIONS["servico"])
        domains = self.db.email_domains(self.company_id)
        suggest = {
            "servico": lambda text: rank_suggestions(services, text),
            "email": lambda text: email_suggestions(domains, text),
        }
        title = f"Editar {row['email']}" if row else "Nova Credencial"
        data = ask_form(self.app, title, CRED_FORM_FIELDS, initial=initial, suggest=suggest)
        if data is not None and not data["login"]:
            data["login"] = data["email"]
        return data

    def db_add(self, data):
        return self.db.add_credential(self.company_id, data)

    def db_update(self, row_id, data):
        self.db.update_credential(row_id, data)

    def db_delete(self, row_id):
        self.db.delete_credential(row_id)

    def row_name(self, row):
        return row["email"]


# --------------------------------------------------------------------------
# Visão da empresa (abas) e visão de Configurações
# --------------------------------------------------------------------------
class CompanyView(ttk.Frame):
    def __init__(self, parent, app):
        super().__init__(parent, style="TFrame")
        self.app = app
        self.columnconfigure(0, weight=1)
        self.rowconfigure(1, weight=1)

        header = ttk.Frame(self, style="TFrame")
        header.grid(row=0, column=0, sticky="ew", padx=28, pady=(22, 10))
        self.title_label = ttk.Label(header, text="", style="Title.TLabel")
        self.title_label.pack(anchor="w")
        self.subtitle_label = ttk.Label(header, text="", style="Muted.TLabel")
        self.subtitle_label.pack(anchor="w")

        self.notebook = ttk.Notebook(self)
        self.notebook.grid(row=1, column=0, sticky="nsew", padx=28, pady=(0, 24))
        self.assets = AssetsPanel(self.notebook, app)
        self.creds = CredentialsPanel(self.notebook, app)
        self.notebook.add(self.assets, text="Infraestrutura / Servidores")
        self.notebook.add(self.creds, text="E-mails e Credenciais")
        self.assets.on_change = self._update_counts
        self.creds.on_change = self._update_counts
        self.notebook.bind("<<NotebookTabChanged>>", lambda e: self.creds.hide_passwords())

    def load(self, company, tab=None):
        """Carrega a empresa. tab: 'assets', 'creds' ou None (mantém a aba atual)."""
        self.title_label.configure(text=company["nome"])
        self.assets.set_company(company["id"])
        self.creds.set_company(company["id"])
        if tab == "assets":
            self.notebook.select(self.assets)
        elif tab == "creds":
            self.notebook.select(self.creds)
        self._update_counts()

    def panel(self, tab):
        return self.creds if tab == "creds" else self.assets

    def _update_counts(self):
        a, c = len(self.assets._rows), len(self.creds._rows)
        self.subtitle_label.configure(text=f"{a} ativo(s)  •  {c} conta(s) de e-mail")
        self.notebook.tab(self.assets, text=f"Infraestrutura / Servidores  ({a})")
        self.notebook.tab(self.creds, text=f"E-mails e Credenciais  ({c})")


class SettingsView(ttk.Frame):
    """Área administrativa: ações destrutivas e de sessão ficam isoladas aqui."""

    def __init__(self, parent, app):
        super().__init__(parent, style="TFrame")
        self.app = app
        self.db = app.db
        self.columnconfigure(0, weight=1)
        self.rowconfigure(2, weight=1)

        head = ttk.Frame(self, style="TFrame")
        head.grid(row=0, column=0, sticky="ew", padx=28, pady=(22, 12))
        ttk.Label(head, text="Configurações / Sistema", style="Title.TLabel").pack(anchor="w")
        ttk.Label(head, text="Área administrativa: as ações desta tela são permanentes.",
                  style="Muted.TLabel").pack(anchor="w")

        # -- Conta e sessão
        card, body = make_card(self, "Conta e sessão")
        card.grid(row=1, column=0, sticky="ew", padx=28, pady=(0, 14))
        self.user_label = ttk.Label(body, text="", style="Card.TLabel")
        self.user_label.pack(anchor="w", pady=(8, 10))
        row = ttk.Frame(body, style="Card.TFrame")
        row.pack(anchor="w")
        ttk.Button(row, text="Alterar minha senha...", style="Tool.TButton",
                   command=self.change_password).pack(side="left")
        ttk.Button(row, text="Sair da conta", style="DangerSoft.TButton",
                   command=self.sign_out).pack(side="left", padx=10)

        # -- Empresas
        card, body = make_card(
            self, "Gerenciar empresas",
            "Selecione uma empresa para renomear ou remover. Remover apaga também todos os "
            "servidores e credenciais dela.")
        card.grid(row=2, column=0, sticky="nsew", padx=28, pady=(0, 14))
        self.tree = ttk.Treeview(body, columns=("nome", "ativos", "contas"), show="headings",
                                 selectmode="browse", height=6)
        for key, title, width, anchor in (("nome", "EMPRESA", 360, "w"),
                                          ("ativos", "SERVIDORES/ATIVOS", 160, "center"),
                                          ("contas", "CONTAS DE E-MAIL", 160, "center")):
            self.tree.heading(key, text=title)
            self.tree.column(key, width=width, anchor=anchor)
        self.tree.tag_configure("odd", background=COLORS["row_alt"])
        self.tree.tag_configure("even", background=COLORS["surface"])
        self.tree.pack(fill="both", expand=True, pady=(12, 10))
        row = ttk.Frame(body, style="Card.TFrame")
        row.pack(anchor="w")
        ttk.Button(row, text="Renomear...", style="Tool.TButton",
                   command=self.rename_company).pack(side="left")
        ttk.Button(row, text="Remover empresa...", style="DangerSoft.TButton",
                   command=self.remove_company).pack(side="left", padx=10)

        # -- Dados
        card, body = make_card(self, "Dados do sistema")
        card.grid(row=3, column=0, sticky="ew", padx=28, pady=(0, 24))
        ttk.Label(body, text=f"Banco de dados: {DB_PATH}", style="CardMuted.TLabel").pack(
            anchor="w", pady=(6, 0))

    def refresh(self):
        self.user_label.configure(text=f"Conectado como:  {self.app.current_user or '-'}")
        self.tree.delete(*self.tree.get_children())
        for i, c in enumerate(self.db.list_companies_with_counts()):
            self.tree.insert("", "end", iid=str(c["id"]), tags=("odd" if i % 2 else "even",),
                             values=(c["nome"], c["ativos"], c["contas"]))

    def _selected_company(self):
        sel = self.tree.selection()
        if not sel:
            self.app.toast("Selecione uma empresa na lista", "warn")
            return None
        return self.db.get_company(int(sel[0]))

    # ---- ações ----------------------------------------------------------------------
    def sign_out(self):
        if messagebox.askyesno("Sair da conta", "Encerrar a sessão atual?", default="no",
                               parent=self.winfo_toplevel()):
            self.app.logout()

    def change_password(self):
        def validate(data):
            if len(data["nova"]) < MIN_PASSWORD_LEN:
                return f"A nova senha deve ter ao menos {MIN_PASSWORD_LEN} caracteres."
            if data["nova"] != data["confirmar"]:
                return "A confirmação não confere com a nova senha."
            if data["nova"] == data["atual"]:
                return "A nova senha deve ser diferente da atual."
            try:    # a troca acontece aqui para a janela continuar aberta se algo falhar
                self.db.change_password(self.app.current_user, data["atual"], data["nova"])
            except ValueError as exc:
                return str(exc)
            return None

        fields = [{"key": "atual", "label": "Senha atual", "kind": "secret", "required": True},
                  {"key": "nova", "label": "Nova senha", "kind": "secret", "required": True},
                  {"key": "confirmar", "label": "Confirmar nova senha", "kind": "secret",
                   "required": True}]
        if ask_form(self.app, "Alterar senha", fields, validate=validate,
                    intro="As senhas do cofre de credenciais continuam acessíveis após a troca."):
            self.app.toast("✔ Senha alterada com sucesso")

    def rename_company(self):
        company = self._selected_company()
        if company is None:
            return
        data = ask_form(self.app, "Renomear empresa",
                        [{"key": "nome", "label": "Novo nome", "required": True}],
                        initial={"nome": company["nome"]})
        if data is None:
            return
        try:
            self.db.rename_company(company["id"], data["nome"])
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicada", f"Já existe uma empresa chamada '{data['nome']}'.",
                                 parent=self.winfo_toplevel())
            return
        self.app.companies_changed()
        self.app.toast("✔ Empresa renomeada")

    def remove_company(self):
        company = self._selected_company()
        if company is None:
            return
        counts = next(c for c in self.db.list_companies_with_counts() if c["id"] == company["id"])
        name = company["nome"]

        def validate(data):
            if data["confirmacao"].casefold() != name.casefold():
                return "O nome digitado não confere com o da empresa."
            return None

        data = ask_form(
            self.app, "Remover empresa",
            [{"key": "confirmacao", "label": f"Digite «{name}»", "required": True}],
            validate=validate, save_text="Remover definitivamente", save_style="Danger.TButton",
            intro=f"Você vai remover PERMANENTEMENTE «{name}», com {counts['ativos']} ativo(s) "
                  f"e {counts['contas']} conta(s) de e-mail. Esta ação não pode ser desfeita.")
        if data is None:
            return
        self.db.delete_company(company["id"])
        self.app.companies_changed(removed_id=company["id"])
        self.app.toast("✔ Empresa removida")


# --------------------------------------------------------------------------
# Base de Conhecimento: Manuais de Apoio (blocos + cartões)
# --------------------------------------------------------------------------
class ManualViewer(tk.Toplevel):
    """Janela de leitura de um manual (caminho + conteúdo) com ações rápidas."""

    def __init__(self, app, manual, on_edit=None):
        super().__init__(app)
        self.app = app
        self.manual = manual
        self.on_edit = on_edit
        self.configure(bg=COLORS["surface"])
        self.title(manual["titulo"])
        self.geometry("740x580")
        self.minsize(560, 420)
        self.transient(app)

        path = (manual["caminho"] or "").strip()
        content = (manual["conteudo"] or "").strip()
        body = ttk.Frame(self, style="Card.TFrame", padding=24)
        body.pack(fill="both", expand=True)
        body.columnconfigure(0, weight=1)
        body.rowconfigure(4, weight=1)

        ttk.Label(body, text=manual["titulo"], style="AuthTitle.TLabel", wraplength=660,
                  justify="left").grid(row=0, column=0, sticky="w")
        ttk.Label(body, style="CardMuted.TLabel",
                  text=f"Bloco: {manual['bloco_nome']}   •   atualizado em {manual['atualizado_em']}"
                  ).grid(row=1, column=0, sticky="w", pady=(2, 12))
        if path:
            ttk.Label(body, text="Caminho / link", style="CardMuted.TLabel").grid(
                row=2, column=0, sticky="w")
            self.path_var = tk.StringVar(value=path)
            ttk.Entry(body, textvariable=self.path_var, state="readonly",
                      font=("Consolas", 10)).grid(row=3, column=0, sticky="ew", pady=(2, 12))

        box = ttk.Frame(body, style="Card.TFrame")
        box.grid(row=4, column=0, sticky="nsew")
        text = tk.Text(box, wrap="word", font=FONT_BASE, relief="solid", bd=1, padx=12, pady=10,
                       bg="white", highlightthickness=0)
        vsb = ttk.Scrollbar(box, orient="vertical", command=text.yview)
        text.configure(yscrollcommand=vsb.set)
        text.pack(side="left", fill="both", expand=True)
        vsb.pack(side="left", fill="y")
        text.insert("1.0", content or "(Este manual não tem conteúdo em texto. "
                                      "Use o caminho/link acima.)")
        text.configure(state="disabled")      # só leitura (ainda dá para selecionar e copiar)

        bar = ttk.Frame(body, style="Card.TFrame")
        bar.grid(row=5, column=0, sticky="ew", pady=(16, 0))
        if path:
            label = "Abrir link" if manual_kind(manual) == "Link" else "Abrir arquivo"
            ttk.Button(bar, text=label, style="Primary.TButton",
                       command=lambda: app.open_manual_file(manual)).pack(side="left")
            ttk.Button(bar, text="Copiar caminho", style="Copy.TButton",
                       command=lambda: app.copy_manual_text(manual, "caminho")).pack(
                side="left", padx=(8, 0))
        if content:
            ttk.Button(bar, text="Copiar conteúdo", style="Copy.TButton",
                       command=lambda: app.copy_manual_text(manual, "conteudo")).pack(
                side="left", padx=(8, 0))
        ttk.Button(bar, text="Fechar", style="Tool.TButton", command=self.destroy).pack(side="right")
        if on_edit:
            ttk.Button(bar, text="Editar", style="Tool.TButton", command=self._edit).pack(
                side="right", padx=(0, 8))

        self.bind("<Escape>", lambda e: self.destroy())
        self.focus_set()

    def _edit(self):
        self.destroy()
        if self.on_edit:
            self.on_edit()


class BlocksDialog(tk.Toplevel):
    """Criar, renomear, reordenar e remover blocos (categorias) de manuais."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.db = app.db
        self.configure(bg=COLORS["surface"])
        self.title("Gerenciar blocos de manuais")
        self.resizable(False, False)
        self.transient(app)

        body = ttk.Frame(self, style="Card.TFrame", padding=24)
        body.pack(fill="both", expand=True)
        ttk.Label(body, text="Blocos / Categorias", style="Section.TLabel").pack(anchor="w")
        ttk.Label(body, style="CardMuted.TLabel", wraplength=580, justify="left",
                  text="Crie, renomeie, reordene ou remova categorias. Remover um bloco "
                       "apaga também todos os manuais dele.").pack(anchor="w", pady=(2, 12))
        self.tree = ttk.Treeview(body, columns=("nome", "qtd"), show="headings",
                                 selectmode="browse", height=9)
        self.tree.heading("nome", text="BLOCO", anchor="w")
        self.tree.heading("qtd", text="MANUAIS", anchor="center")
        self.tree.column("nome", width=470, anchor="w")
        self.tree.column("qtd", width=110, anchor="center")
        self.tree.tag_configure("odd", background=COLORS["row_alt"])
        self.tree.tag_configure("even", background=COLORS["surface"])
        self.tree.pack(fill="x")

        bar = ttk.Frame(body, style="Card.TFrame")
        bar.pack(fill="x", pady=(14, 0))
        ttk.Button(bar, text="+ Novo bloco", style="Primary.TButton",
                   command=self.new_block).pack(side="left")
        ttk.Button(bar, text="Renomear", style="Tool.TButton",
                   command=self.rename_block).pack(side="left", padx=8)
        ttk.Button(bar, text="▲", width=3, style="Tool.TButton",
                   command=lambda: self.move(-1)).pack(side="left")
        ttk.Button(bar, text="▼", width=3, style="Tool.TButton",
                   command=lambda: self.move(1)).pack(side="left", padx=(4, 0))
        ttk.Button(bar, text="Remover", style="DangerSoft.TButton",
                   command=self.remove_block).pack(side="left", padx=8)
        ttk.Button(bar, text="Fechar", style="Tool.TButton", command=self.destroy).pack(side="right")

        self.refresh()
        self.bind("<Escape>", lambda e: self.destroy())
        self.update_idletasks()
        x = app.winfo_rootx() + (app.winfo_width() - self.winfo_width()) // 2
        y = app.winfo_rooty() + (app.winfo_height() - self.winfo_height()) // 3
        self.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        self._grab()

    def _grab(self):
        try:
            self.wait_visibility()
            self.grab_set()
        except tk.TclError:
            pass

    def _ask(self, *args, **kwargs):
        """Abre um formulário por cima desta janela e devolve o modal ao terminar."""
        result = ask_form(self, *args, **kwargs)
        self._grab()
        return result

    def refresh(self, select_id=None):
        self.tree.delete(*self.tree.get_children())
        for i, b in enumerate(self.db.list_blocks_with_counts()):
            self.tree.insert("", "end", iid=str(b["id"]), values=(b["nome"], b["manuais"]),
                             tags=("odd" if i % 2 else "even",))
        if select_id is not None and self.tree.exists(str(select_id)):
            self.tree.selection_set(str(select_id))

    def _selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Blocos", "Selecione um bloco na lista.", parent=self)
            return None
        return self.db.get_block(int(sel[0]))

    def new_block(self):
        data = self._ask("Novo bloco", [{"key": "nome", "label": "Nome do bloco",
                                         "required": True}])
        if data is None:
            return
        try:
            new_id = self.db.add_block(data["nome"])
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicado", f"Já existe um bloco chamado '{data['nome']}'.",
                                 parent=self)
            return
        self.refresh(select_id=new_id)

    def rename_block(self):
        block = self._selected()
        if block is None:
            return
        data = self._ask("Renomear bloco", [{"key": "nome", "label": "Novo nome",
                                             "required": True}], initial={"nome": block["nome"]})
        if data is None:
            return
        try:
            self.db.rename_block(block["id"], data["nome"])
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicado", f"Já existe um bloco chamado '{data['nome']}'.",
                                 parent=self)
            return
        self.refresh(select_id=block["id"])

    def move(self, delta):
        block = self._selected()
        if block is None:
            return
        self.db.move_block(block["id"], delta)
        self.refresh(select_id=block["id"])

    def remove_block(self):
        block = self._selected()
        if block is None:
            return
        total = next(b["manuais"] for b in self.db.list_blocks_with_counts()
                     if b["id"] == block["id"])
        name = block["nome"]
        if total:
            def validate(data):
                if data["confirmacao"].casefold() != name.casefold():
                    return "O nome digitado não confere com o do bloco."
                return None

            data = self._ask(
                "Remover bloco", [{"key": "confirmacao", "label": f"Digite «{name}»",
                                   "required": True}],
                validate=validate, save_text="Remover definitivamente",
                save_style="Danger.TButton",
                intro=f"Você vai remover PERMANENTEMENTE o bloco «{name}» e seus {total} "
                      "manual(is). Esta ação não pode ser desfeita.")
            if data is None:
                return
        elif not messagebox.askyesno("Remover bloco", f"Remover o bloco vazio «{name}»?",
                                     default="no", parent=self):
            return
        self.db.delete_block(block["id"])
        self.refresh()


class ManualsView(ttk.Frame):
    """Tela 'Manuais de Apoio': blocos (categorias) com cartões de manuais."""

    def __init__(self, parent, app):
        super().__init__(parent, style="TFrame")
        self.app = app
        self.db = app.db
        self._cols = 0
        self._groups = []         # [(frame da grade, [cartões])]
        self._cards = {}          # id do manual -> cartão
        self._sections = {}       # id do bloco -> seção
        self._block_titles = {}   # id do bloco -> rótulo do título
        self._wrap_labels = []    # [(rótulo, deslocamento)] p/ quebrar o texto pela largura
        self.columnconfigure(0, weight=1)
        self.rowconfigure(1, weight=1)

        head = ttk.Frame(self, style="TFrame")
        head.grid(row=0, column=0, sticky="ew", padx=28, pady=(22, 12))
        left = ttk.Frame(head, style="TFrame")
        left.pack(side="left")
        ttk.Label(left, text="Manuais e Procedimentos", style="Title.TLabel").pack(anchor="w")
        self.subtitle = ttk.Label(left, text="", style="Muted.TLabel")
        self.subtitle.pack(anchor="w")
        right = ttk.Frame(head, style="TFrame")
        right.pack(side="right")
        ttk.Button(right, text="+ Novo Manual", style="Primary.TButton",
                   command=self.add_manual).pack(side="left")
        ttk.Button(right, text="Gerenciar Blocos", style="Tool.TButton",
                   command=self.manage_blocks).pack(side="left", padx=(10, 0))

        self.scroll = ScrollFrame(self, COLORS["bg"])
        self.scroll.grid(row=1, column=0, sticky="nsew", padx=(28, 18), pady=(0, 20))
        self.scroll.on_width = self._on_width

    # ---- desenho ------------------------------------------------------------------
    def refresh(self):
        inner = self.scroll.inner
        for w in inner.winfo_children():
            w.destroy()
        self._groups, self._cards, self._sections = [], {}, {}
        self._block_titles, self._wrap_labels = {}, []
        blocks = self.db.list_blocks()
        manuals = self.db.list_manuals()
        by_block = {}
        for m in manuals:
            by_block.setdefault(m["bloco_id"], []).append(m)
        self.subtitle.configure(text=f"{len(blocks)} bloco(s)  •  {len(manuals)} manual(is)")
        if not blocks:
            tk.Label(inner, text="Nenhum bloco criado ainda.\nClique em «Gerenciar Blocos» para "
                                 "criar o primeiro.", bg=COLORS["bg"], fg=COLORS["muted"],
                     font=(FONT, 12), justify="left").pack(anchor="w", pady=20)
            return
        for block in blocks:
            self._build_block(inner, block, by_block.get(block["id"], []))
        self._layout(force=True)

    def _build_block(self, inner, block, manuals):
        c = COLORS
        section = tk.Frame(inner, bg=c["bg"])
        section.pack(fill="x", pady=(0, 26))
        self._sections[block["id"]] = section
        head = tk.Frame(section, bg=c["bg"])
        head.pack(fill="x")
        title = tk.Label(head, text=block["nome"], bg=c["bg"], fg=c["text"],
                         font=(FONT, 16, "bold"))
        title.pack(side="left")
        self._block_titles[block["id"]] = title
        tk.Label(head, text=f"{len(manuals)} manual(is)", bg=c["bg"], fg=c["muted"],
                 font=(FONT, 10)).pack(side="left", padx=12, pady=(5, 0))
        ttk.Button(head, text="+ Adicionar neste bloco", style="ToolSm.TButton",
                   command=lambda bid=block["id"]: self.add_manual(bid)).pack(side="right")
        tk.Frame(section, bg=c["border"], height=1).pack(fill="x", pady=(8, 12))
        grid = tk.Frame(section, bg=c["bg"])
        grid.pack(fill="x")
        cards = []
        if not manuals:
            tk.Label(grid, text="Nenhum manual neste bloco ainda.", bg=c["bg"], fg=c["muted"],
                     font=(FONT, 11)).grid(row=0, column=0, sticky="w")
        for m in manuals:
            card = self._build_card(grid, m)
            cards.append(card)
            self._cards[m["id"]] = card
        self._groups.append((grid, cards))

    def _build_card(self, parent, m):
        c = COLORS
        mid = m["id"]
        card = tk.Frame(parent, bg=c["surface"], highlightbackground=c["border"],
                        highlightcolor=c["border"], highlightthickness=2)
        body = ttk.Frame(card, style="Card.TFrame", padding=(16, 14))
        body.pack(fill="both", expand=True)
        body.columnconfigure(0, weight=1)

        title = ttk.Label(body, text=m["titulo"], style="CardTitle.TLabel", justify="left",
                          cursor="hand2")
        title.grid(row=0, column=0, sticky="nw")
        title.bind("<Button-1>", lambda e, mid=mid: self.view_manual(mid))
        self._wrap_labels.append((title, 190))
        tools = ttk.Frame(body, style="Card.TFrame")
        tools.grid(row=0, column=1, sticky="ne", padx=(8, 0))
        ttk.Button(tools, text="Editar", style="ToolSm.TButton",
                   command=lambda mid=mid: self.edit_manual(mid)).pack(side="left")
        ttk.Button(tools, text="Remover", style="DangerSoftSm.TButton",
                   command=lambda mid=mid: self.remove_manual(mid)).pack(side="left", padx=(6, 0))

        kind = manual_kind(m)
        ttk.Label(body, text=kind.upper(), style="Chip.TLabel").grid(
            row=1, column=0, columnspan=2, sticky="w", pady=(8, 8))
        summary = " ".join((m["conteudo"] or "").split())
        if len(summary) > 170:
            summary = summary[:167] + "…"
        row = 2
        if summary:
            lbl = ttk.Label(body, text=summary, style="CardMuted.TLabel", justify="left")
            lbl.grid(row=row, column=0, columnspan=2, sticky="w")
            self._wrap_labels.append((lbl, 36))
            row += 1
        if m["caminho"]:
            ttk.Label(body, text=short_path(m["caminho"], 58), style="Path.TLabel").grid(
                row=row, column=0, columnspan=2, sticky="w", pady=(6, 0))
            row += 1

        actions = ttk.Frame(body, style="Card.TFrame")
        actions.grid(row=row, column=0, columnspan=2, sticky="w", pady=(12, 0))
        if m["caminho"]:
            label = "Abrir link" if kind == "Link" else "Abrir arquivo"
            ttk.Button(actions, text=label, style="PrimarySm.TButton",
                       command=lambda mid=mid: self.open_manual(mid)).pack(side="left")
        if m["conteudo"]:
            ttk.Button(actions, text="Ver conteúdo",
                       style="ToolSm.TButton" if m["caminho"] else "PrimarySm.TButton",
                       command=lambda mid=mid: self.view_manual(mid)).pack(side="left", padx=(6, 0))
        copy_bar = ttk.Frame(body, style="Card.TFrame")
        copy_bar.grid(row=row + 1, column=0, columnspan=2, sticky="w", pady=(8, 0))
        ttk.Label(copy_bar, text="Copiar:", style="CardMuted.TLabel").pack(side="left")
        if m["caminho"]:
            ttk.Button(copy_bar, text="Caminho", style="CopySm.TButton",
                       command=lambda mid=mid: self.copy_manual(mid, "caminho")).pack(
                side="left", padx=(6, 0))
        if m["conteudo"]:
            ttk.Button(copy_bar, text="Conteúdo", style="CopySm.TButton",
                       command=lambda mid=mid: self.copy_manual(mid, "conteudo")).pack(
                side="left", padx=(6, 0))
        return card

    def _on_width(self, width):
        self._layout(width)

    def _layout(self, width=None, force=False):
        """Reorganiza os cartões em 1 a 3 colunas conforme a largura da janela."""
        if width is None:
            width = self.scroll.canvas.winfo_width()
        cols = max(1, min(3, width // 420))
        card_w = max(240, width // cols - 24)
        for label, offset in self._wrap_labels:
            label.configure(wraplength=max(120, card_w - offset))
        if cols == self._cols and not force:
            return
        self._cols = cols
        for grid, cards in self._groups:
            for col in range(3):
                grid.columnconfigure(col, weight=1 if col < cols else 0,
                                     uniform="cards" if col < cols else "")
            for i, card in enumerate(cards):
                card.grid(row=i // cols, column=i % cols, sticky="nsew", padx=6, pady=6)

    # ---- navegação (vindo da busca) ----------------------------------------------------
    def _scroll_to(self, widget):
        self.update_idletasks()
        y, w = 0, widget
        while w is not None and w is not self.scroll.inner:
            y += w.winfo_y()
            w = w.master
        total = max(1, self.scroll.inner.winfo_height())
        self.scroll.canvas.yview_moveto(max(0.0, (y - 12) / total))

    def focus_manual(self, manual_id):
        card = self._cards.get(manual_id)
        if card is None:
            return
        self._scroll_to(card)
        card.configure(highlightbackground=COLORS["primary"], highlightcolor=COLORS["primary"])
        self.after(2600, lambda: self._unflash(card))

    @staticmethod
    def _unflash(card):
        try:
            card.configure(highlightbackground=COLORS["border"], highlightcolor=COLORS["border"])
        except tk.TclError:
            pass

    def focus_block(self, block_id):
        section, title = self._sections.get(block_id), self._block_titles.get(block_id)
        if section is None:
            return
        self._scroll_to(section)
        title.configure(fg=COLORS["primary"])
        self.after(2600, lambda: self._unflash_title(title))

    @staticmethod
    def _unflash_title(label):
        try:
            label.configure(fg=COLORS["text"])
        except tk.TclError:
            pass

    # ---- ações ---------------------------------------------------------------------------
    def manage_blocks(self):
        dialog = BlocksDialog(self.app)
        self.app.wait_window(dialog)
        self.refresh()

    def _ask_manual(self, row, default_block_id=None):
        blocks = self.db.list_blocks()
        names = [b["nome"] for b in blocks]
        ids = {b["nome"].casefold(): b["id"] for b in blocks}
        if row:
            initial = {"bloco": row["bloco_nome"], "titulo": row["titulo"],
                       "caminho": row["caminho"], "conteudo": row["conteudo"]}
        else:
            default = next((b["nome"] for b in blocks if b["id"] == default_block_id), names[0])
            initial = {"bloco": default}
        fields = [
            {"key": "bloco", "kind": "choice", "choices": names, "required": True},
            {"key": "titulo", "label": "Título do manual", "required": True},
            {"key": "caminho", "kind": "path", "label": "Caminho do arquivo ou link"},
            {"key": "conteudo", "kind": "text", "label": "Conteúdo / passo a passo"},
        ]

        def validate(data):
            if not data["caminho"] and not data["conteudo"]:
                return "Informe o caminho do arquivo (ou link) e/ou escreva o conteúdo do manual."
            return None

        title = f"Editar «{row['titulo']}»" if row else "Novo manual"
        data = ask_form(self.app, title, fields, initial=initial, validate=validate,
                        intro="Salve o caminho de um arquivo na rede, um link e/ou escreva o "
                              "passo a passo aqui mesmo. Não coloque senhas neste campo.")
        if data is None:
            return None
        data["bloco_id"] = ids[data["bloco"].casefold()]
        data["caminho"] = data["caminho"].strip().strip('"')
        return data

    def add_manual(self, block_id=None):
        if not self.db.list_blocks():
            self.app.toast("Crie um bloco antes de adicionar manuais", "warn")
            self.manage_blocks()
            return
        data = self._ask_manual(None, block_id)
        if data is None:
            return
        try:
            new_id = self.db.add_manual(data["bloco_id"], data["titulo"], data["caminho"],
                                        data["conteudo"])
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicado", f"Já existe um manual '{data['titulo']}' neste bloco.",
                                 parent=self.app)
            return
        self.refresh()
        self.app.toast("✔ Manual salvo")
        self.after(80, lambda: self.focus_manual(new_id))

    def edit_manual(self, manual_id):
        row = self.db.get_manual(manual_id)
        if row is None:
            self.refresh()
            return
        data = self._ask_manual(row)
        if data is None:
            return
        try:
            self.db.update_manual(manual_id, data["bloco_id"], data["titulo"], data["caminho"],
                                  data["conteudo"])
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicado", f"Já existe um manual '{data['titulo']}' neste bloco.",
                                 parent=self.app)
            return
        self.refresh()
        self.app.toast("✔ Manual atualizado")
        self.after(80, lambda: self.focus_manual(manual_id))

    def remove_manual(self, manual_id):
        row = self.db.get_manual(manual_id)
        if row is None:
            return
        if not messagebox.askyesno("Remover manual", f"Remover o manual «{row['titulo']}»?\n\n"
                                   "Esta ação não pode ser desfeita.", icon="warning",
                                   default="no", parent=self.app):
            return
        self.db.delete_manual(manual_id)
        self.refresh()
        self.app.toast("✔ Manual removido")

    def view_manual(self, manual_id):
        row = self.db.get_manual(manual_id)
        if row is not None:
            ManualViewer(self.app, row, on_edit=lambda: self.edit_manual(manual_id))

    def open_manual(self, manual_id):
        row = self.db.get_manual(manual_id)
        if row is not None:
            self.app.open_manual_file(row)

    def copy_manual(self, manual_id, field):
        row = self.db.get_manual(manual_id)
        if row is not None:
            self.app.copy_manual_text(row, field)


# --------------------------------------------------------------------------
# Aplicação
# --------------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Gerenciador de Infraestrutura de TI")
        self.geometry("1360x800")
        self.minsize(1120, 660)
        self.configure(bg=COLORS["bg"])
        self.option_add("*TCombobox*Listbox.font", FONT_BASE)
        # Emoji fora do plano básico só em Tk >= 8.6.10; antes disso usa um símbolo simples.
        try:
            patch = tuple(int(x) for x in str(self.tk.call("info", "patchlevel")).split(".")[:3])
        except (tk.TclError, ValueError):
            patch = (8, 6, 0)
        self.icon_books = "📚" if patch >= (8, 6, 10) else "▤"
        self._setup_styles()

        self.db = Database(DB_PATH)
        self.current_user = None
        self.current_company = None
        self.section = "none"        # none | company | manuals | settings
        self.company_buttons = {}
        self.search_results = []
        self.failed_attempts = 0
        self.container = None
        self.views = {}
        self._toast_label = None
        self._toast_job = None
        self._clip_job = None
        self._clip_text = None

        self.protocol("WM_DELETE_WINDOW", self._on_close)

        # Fluxo de inicialização: banco existe? -> login; senão -> primeiro acesso
        if self.db.is_ready():
            self.show_login()
        else:
            self.show_setup()

    # ---- estilo ---------------------------------------------------------------
    def _setup_styles(self):
        c = COLORS
        style = ttk.Style(self)
        if "clam" in style.theme_names():
            style.theme_use("clam")
        style.configure(".", font=FONT_BASE, background=c["bg"], foreground=c["text"])
        style.configure("TFrame", background=c["bg"])
        style.configure("Surface.TFrame", background=c["surface"])
        style.configure("Card.TFrame", background=c["surface"])
        style.configure("TLabel", background=c["bg"], foreground=c["text"])
        style.configure("Card.TLabel", background=c["surface"])
        style.configure("CardMuted.TLabel", background=c["surface"], foreground=c["muted"])
        style.configure("Muted.TLabel", background=c["bg"], foreground=c["muted"])
        style.configure("Title.TLabel", background=c["bg"], font=(FONT, 20, "bold"))
        style.configure("AuthTitle.TLabel", background=c["surface"], font=(FONT, 20, "bold"))
        style.configure("Section.TLabel", background=c["surface"], font=(FONT, 14, "bold"))
        style.configure("Card.TCheckbutton", background=c["surface"], foreground=c["text"])
        style.map("Card.TCheckbutton", background=[("active", c["surface"])])

        for name in ("TEntry", "TCombobox"):
            style.configure(name, padding=7, fieldbackground="white", bordercolor=c["border"],
                            lightcolor=c["border"], darkcolor=c["border"])
            style.map(name, bordercolor=[("focus", c["primary"])],
                      lightcolor=[("focus", c["primary"])], darkcolor=[("focus", c["primary"])])
        style.map("TCombobox", fieldbackground=[("readonly", "white")])

        def button(name, bg, fg, hover, border=None, padding=(14, 8), size=10):
            style.configure(name, background=bg, foreground=fg, bordercolor=border or bg,
                            lightcolor=bg, darkcolor=bg, focuscolor=bg, relief="flat",
                            padding=padding, font=(FONT, size, "bold"))
            style.map(name, background=[("disabled", c["border"]), ("pressed", hover),
                                        ("active", hover)],
                      foreground=[("disabled", c["muted"])])

        button("Primary.TButton", c["primary"], "white", c["primary_hover"])
        button("Danger.TButton", c["danger"], "white", c["danger_hover"])
        button("Tool.TButton", c["head"], c["text"], c["border"], c["border"])
        button("Copy.TButton", "#DBEAFE", c["primary"], "#BFDBFE", "#BFDBFE")
        button("DangerSoft.TButton", c["danger_soft"], c["danger"], "#FECACA", "#FECACA")
        small = {"padding": (10, 5), "size": 9}          # variações compactas (cartões)
        button("PrimarySm.TButton", c["primary"], "white", c["primary_hover"], **small)
        button("ToolSm.TButton", c["head"], c["text"], c["border"], c["border"], **small)
        button("CopySm.TButton", "#DBEAFE", c["primary"], "#BFDBFE", "#BFDBFE", **small)
        button("DangerSoftSm.TButton", c["danger_soft"], c["danger"], "#FECACA", "#FECACA", **small)
        style.configure("CardTitle.TLabel", background=c["surface"], font=(FONT, 12, "bold"))
        style.configure("Chip.TLabel", background="#DBEAFE", foreground=c["primary"],
                        font=(FONT, 8, "bold"), padding=(8, 2))
        style.configure("Path.TLabel", background=c["surface"], foreground=c["muted"],
                        font=("Consolas", 9))

        style.configure("Treeview", font=(FONT, 11), rowheight=36, background=c["surface"],
                        fieldbackground=c["surface"], foreground=c["text"],
                        bordercolor=c["border"], lightcolor=c["border"], darkcolor=c["border"])
        style.configure("Treeview.Heading", font=(FONT, 10, "bold"), background=c["head"],
                        foreground=c["text"], padding=(10, 9), relief="flat")
        style.map("Treeview.Heading", background=[("active", c["border"])])
        style.map("Treeview", background=[("selected", c["primary"])],
                  foreground=[("selected", "white")])

        style.configure("TNotebook", background=c["bg"], borderwidth=0, tabmargins=(0, 4, 0, 0))
        style.configure("TNotebook.Tab", font=(FONT, 11, "bold"), padding=(24, 11),
                        background=c["head"], foreground=c["muted"], borderwidth=0)
        style.map("TNotebook.Tab", background=[("selected", c["surface"]), ("active", c["border"])],
                  foreground=[("selected", c["primary"])])

    def _reset_container(self):
        self._unbind_wheel_force()
        if self.container is not None:
            self.container.destroy()
        self.container = ttk.Frame(self)
        self.container.pack(fill="both", expand=True)
        self.views = {}
        self.company_buttons = {}
        return self.container

    def _auth_card(self, title, subtitle):
        """Cartão central das telas de login/primeiro acesso. Retorna o corpo."""
        root = self._reset_container()
        card = tk.Frame(root, bg=COLORS["surface"], highlightbackground=COLORS["border"],
                        highlightthickness=1)
        card.place(relx=0.5, rely=0.5, anchor="center")
        body = ttk.Frame(card, style="Card.TFrame", padding=36)
        body.pack()
        ttk.Label(body, text=title, style="AuthTitle.TLabel").grid(
            row=0, column=0, columnspan=2, pady=(0, 4))
        ttk.Label(body, text=subtitle, style="CardMuted.TLabel", justify="center").grid(
            row=1, column=0, columnspan=2, pady=(0, 20))
        return body

    def _on_close(self):
        self._clear_clipboard_now()
        if self.db.conn is not None:
            self.db.conn.close()
        self.destroy()

    def report_callback_exception(self, exc, val, tb):
        """Erros dentro de botões/eventos: grava em data/erro.log e avisa na tela."""
        import traceback
        text = "".join(traceback.format_exception(exc, val, tb))
        try:
            DATA_DIR.mkdir(parents=True, exist_ok=True)
            with open(ERROR_LOG, "a", encoding="utf-8") as fh:
                fh.write(text + "\n")
        except OSError:
            pass
        try:
            messagebox.showerror("Erro inesperado",
                                 f"{val}\n\nDetalhes gravados em:\n{ERROR_LOG}")
        except tk.TclError:
            pass

    # ---- aviso rápido (toast) e área de transferência -----------------------------------
    def toast(self, message, kind="ok"):
        """Mensagem rápida no rodapé da janela (some sozinha em ~2 s)."""
        color = {"ok": COLORS["toast"], "warn": COLORS["warn"], "error": COLORS["danger"]}[kind]
        if self._toast_label is None or not self._toast_label.winfo_exists():
            self._toast_label = tk.Label(self, font=(FONT, 11, "bold"), fg="white",
                                         padx=20, pady=11)
        self._toast_label.configure(text=message, bg=color)
        self._toast_label.place(relx=0.5, rely=1.0, y=-34, anchor="s")
        self._toast_label.lift()
        if self._toast_job is not None:
            self.after_cancel(self._toast_job)
        self._toast_job = self.after(2200, self._hide_toast)

    def _hide_toast(self):
        self._toast_job = None
        if self._toast_label is not None and self._toast_label.winfo_exists():
            self._toast_label.place_forget()

    def copy_to_clipboard(self, text, label, sensitive=False):
        """Copia e avisa. Senhas somem da área de transferência após 30 s."""
        try:
            self.clipboard_clear()
            self.clipboard_append(text)
            self.update()      # grava de fato na área de transferência do sistema
        except tk.TclError:
            self.toast("Não foi possível copiar", "error")
            return
        if self._clip_job is not None:
            self.after_cancel(self._clip_job)
            self._clip_job = None
        if sensitive:
            self._clip_text = text
            self._clip_job = self.after(CLIPBOARD_CLEAR_MS, self._clear_clipboard_if_unchanged)
            self.toast(f"✔ {label} copiada (será limpa em {CLIPBOARD_CLEAR_MS // 1000} s)")
        else:
            self._clip_text = None
            flat = " ".join(text.split())
            shown = flat if len(flat) <= 40 else flat[:37] + "…"
            self.toast(f"✔ {label} copiado: {shown}")

    def _clear_clipboard_if_unchanged(self):
        self._clip_job = None
        self._clear_clipboard_now()

    def _clear_clipboard_now(self):
        """Limpa a área de transferência se ela ainda tiver a senha copiada por nós."""
        if self._clip_text is None:
            return
        try:
            if self.clipboard_get() == self._clip_text:
                self.clipboard_clear()
                self.update()
        except tk.TclError:
            pass
        self._clip_text = None

    # ---- manuais: abrir arquivo e copiar (usados pelos cartões e pelo visualizador) ----
    def open_manual_file(self, manual):
        target = (manual["caminho"] or "").strip()
        if not target:
            self.toast("Este manual não tem arquivo/link. Use «Ver conteúdo».", "warn")
            return
        error = open_path(target)
        if error:
            messagebox.showwarning("Não foi possível abrir", error, parent=self)
        else:
            self.toast(f"✔ Abrindo: {short_path(target, 45)}")

    def copy_manual_text(self, manual, field):
        text = (manual[field] or "").strip()
        label = "Caminho" if field == "caminho" else "Conteúdo"
        if not text:
            self.toast(f"{label} vazio neste manual", "warn")
            return
        self.copy_to_clipboard(text, label)

    # ---- tela: primeiro acesso -------------------------------------------------
    def show_setup(self):
        body = self._auth_card("Primeiro Acesso",
                               f"Crie o usuário master. O banco de dados será gerado em\n{DB_PATH}")
        user_var, pw_var, pw2_var = tk.StringVar(), tk.StringVar(), tk.StringVar()
        entries = []
        for i, (label, var, show) in enumerate(
                [("Usuário", user_var, ""), ("Senha", pw_var, "•"),
                 ("Confirmar senha", pw2_var, "•")], start=2):
            ttk.Label(body, text=label, style="Card.TLabel").grid(
                row=i, column=0, sticky="w", pady=7, padx=(0, 14))
            e = ttk.Entry(body, textvariable=var, show=show, width=30, font=(FONT, 12))
            e.grid(row=i, column=1, pady=7)
            entries.append(e)
        entries[0].focus_set()

        def create():
            username, pw, pw2 = user_var.get().strip(), pw_var.get(), pw2_var.get()
            if not username:
                messagebox.showwarning("Atenção", "Informe o nome de usuário.")
                return
            if len(pw) < MIN_PASSWORD_LEN:
                messagebox.showwarning("Senha fraca",
                                       f"A senha deve ter ao menos {MIN_PASSWORD_LEN} caracteres.")
                return
            if pw != pw2:
                messagebox.showwarning("Atenção", "A confirmação não confere com a senha.")
                return
            try:
                self.db.initialize()                  # cria pasta + .db + tabelas
                self.db.create_user(username, pw)     # salva SOMENTE o hash e o cofre embrulhado
            except (sqlite3.Error, OSError) as exc:
                messagebox.showerror("Erro", f"Não foi possível criar o banco:\n{exc}")
                return
            messagebox.showinfo("Pronto", "Conta criada com sucesso. Faça login.")
            self.show_login()

        ttk.Button(body, text="Criar conta", style="Primary.TButton", command=create).grid(
            row=5, column=0, columnspan=2, sticky="ew", pady=(18, 0))
        for e in entries:
            e.bind("<Return>", lambda ev: create())

    # ---- tela: login ------------------------------------------------------------
    def show_login(self):
        body = self._auth_card("Infraestrutura de TI", "Entre com suas credenciais")
        user_var, pw_var = tk.StringVar(), tk.StringVar()
        ttk.Label(body, text="Usuário", style="Card.TLabel").grid(
            row=2, column=0, sticky="w", pady=7, padx=(0, 14))
        e_user = ttk.Entry(body, textvariable=user_var, width=30, font=(FONT, 12))
        e_user.grid(row=2, column=1, pady=7)
        ttk.Label(body, text="Senha", style="Card.TLabel").grid(
            row=3, column=0, sticky="w", pady=7, padx=(0, 14))
        e_pw = ttk.Entry(body, textvariable=pw_var, show="•", width=30, font=(FONT, 12))
        e_pw.grid(row=3, column=1, pady=7)
        e_user.focus_set()

        btn = ttk.Button(body, text="Entrar", style="Primary.TButton")
        btn.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(18, 0))

        def attempt():
            if str(btn["state"]) == "disabled":
                return
            username = user_var.get().strip()
            if self.db.login(username, pw_var.get()):
                self.failed_attempts = 0
                self.current_user = username
                self.show_main()
                return
            self.failed_attempts += 1
            pw_var.set("")
            messagebox.showerror("Acesso negado", "Usuário ou senha incorretos.")
            if self.failed_attempts >= 3:     # freio simples contra força bruta
                btn.state(["disabled"])
                self.after(5000, lambda: btn.winfo_exists() and btn.state(["!disabled"]))
            e_pw.focus_set()

        btn.configure(command=attempt)
        e_user.bind("<Return>", lambda ev: e_pw.focus_set())
        e_pw.bind("<Return>", lambda ev: attempt())

    def logout(self):
        self._clear_clipboard_now()
        self.db.logout()                 # descarta a chave do cofre da memória
        self.current_user = None
        self.current_company = None
        self.section = "none"
        self._hide_toast()
        self.show_login()

    # ---- tela principal -----------------------------------------------------------
    def show_main(self):
        root = self._reset_container()
        self.current_company = None
        self.section = "none"
        root.rowconfigure(1, weight=1)
        root.columnconfigure(1, weight=1)

        self._build_sidebar(root)
        self._build_topbar(root)

        # Área de conteúdo: três visões empilhadas (só uma fica por cima)
        self.content = ttk.Frame(root, style="TFrame")
        self.content.grid(row=1, column=1, sticky="nsew")
        self.content.rowconfigure(0, weight=1)
        self.content.columnconfigure(0, weight=1)
        placeholder = ttk.Frame(self.content, style="TFrame")
        ttk.Label(placeholder, justify="center", style="Muted.TLabel", font=(FONT, 13),
                  text="Selecione uma empresa no menu à esquerda, abra os Manuais de Apoio\n"
                       "ou pesquise por hostname, IP, AnyDesk, e-mail ou manual (Ctrl+F).").place(
            relx=0.5, rely=0.42, anchor="center")
        self.company_view = CompanyView(self.content, self)
        self.settings_view = SettingsView(self.content, self)
        self.manuals_view = ManualsView(self.content, self)
        self.views = {"placeholder": placeholder, "company": self.company_view,
                      "settings": self.settings_view, "manuals": self.manuals_view}
        for view in self.views.values():
            view.grid(row=0, column=0, sticky="nsew")

        # Lista de resultados da pesquisa (aparece sob o campo de busca)
        self.search_list = tk.Listbox(root, height=8, font=FONT_BASE, activestyle="none",
                                      relief="solid", bd=1, highlightthickness=0,
                                      selectbackground=COLORS["primary"], selectforeground="white")
        self.search_list.bind("<ButtonRelease-1>", self._on_search_pick)
        self.search_list.bind("<Return>", self._on_search_pick)
        self.search_list.bind("<Escape>", lambda e: self._hide_search())

        self.bind("<Control-f>", self._focus_search)
        self.refresh_companies()
        self.show_view("placeholder")

    def show_view(self, name):
        self.views[name].tkraise()

    def _build_topbar(self, root):
        top = tk.Frame(root, bg=COLORS["surface"])
        top.grid(row=0, column=1, sticky="ew")
        inner = tk.Frame(top, bg=COLORS["surface"])
        inner.pack(fill="x", padx=28, pady=14)
        ttk.Label(inner, text="Pesquisar", style="Card.TLabel", font=FONT_BOLD).pack(side="left")
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(inner, textvariable=self.search_var, width=48,
                                      font=(FONT, 12))
        self.search_entry.pack(side="left", padx=12)
        ttk.Label(inner, text="hostname, IP, AnyDesk, e-mail, manuais…   (Ctrl+F)",
                  style="CardMuted.TLabel").pack(side="left")
        ttk.Label(inner, text=f"Usuário: {self.current_user}",
                  style="CardMuted.TLabel").pack(side="right")
        tk.Frame(top, bg=COLORS["border"], height=1).pack(fill="x")

        self.search_entry.bind("<KeyRelease>", self._on_search_key)
        self.search_entry.bind("<Return>", self._on_search_enter)
        self.search_entry.bind("<Escape>", lambda e: self._hide_search())

    def _focus_search(self, _event=None):
        try:
            self.search_entry.focus_set()
            self.search_entry.selection_range(0, "end")
        except (AttributeError, tk.TclError):
            pass
        return "break"

    def _hover(self, widget, normal, active_fn, hover=None):
        """Efeito de passar o mouse nos botões do menu lateral."""
        hover = hover or COLORS["side_hover"]
        widget.bind("<Enter>", lambda e: widget.configure(
            bg=COLORS["side_sel"] if active_fn() else hover))
        widget.bind("<Leave>", lambda e: widget.configure(
            bg=COLORS["side_sel"] if active_fn() else normal))

    def _build_sidebar(self, root):
        c = COLORS
        side = tk.Frame(root, bg=c["side"], width=292)
        side.grid(row=0, column=0, rowspan=2, sticky="ns")
        side.grid_propagate(False)
        side.columnconfigure(0, weight=1)
        side.rowconfigure(5, weight=1)

        tk.Label(side, text="Painel de TI", bg=c["side"], fg="white", anchor="w",
                 font=(FONT, 18, "bold")).grid(row=0, column=0, columnspan=2, sticky="ew",
                                               padx=20, pady=(22, 0))
        tk.Label(side, text="Gestão de infraestrutura", bg=c["side"], fg=c["side_muted"],
                 anchor="w", font=(FONT, 10)).grid(row=1, column=0, columnspan=2, sticky="ew",
                                                   padx=20)
        add_btn = tk.Button(side, text="+  Adicionar Nova Empresa", command=self.add_company,
                            bg=c["success"], fg="white", activebackground=c["success_hover"],
                            activeforeground="white", relief="flat", bd=0, cursor="hand2",
                            font=(FONT, 12, "bold"), pady=13)
        add_btn.grid(row=2, column=0, columnspan=2, sticky="ew", padx=14, pady=(18, 14))
        add_btn.bind("<Enter>", lambda e: add_btn.configure(bg=c["success_hover"]))
        add_btn.bind("<Leave>", lambda e: add_btn.configure(bg=c["success"]))
        self.manuals_btn = tk.Button(
            side, text=f"{self.icon_books}   Manuais de Apoio", anchor="w",
            command=self.open_manuals, bg=c["side_hover"], fg=c["side_fg"],
            activebackground=c["side_sel"], activeforeground="white", relief="flat", bd=0,
            cursor="hand2", font=(FONT, 12, "bold"), padx=16, pady=12)
        self.manuals_btn.grid(row=3, column=0, columnspan=2, sticky="ew", padx=14, pady=(0, 16))
        self._hover(self.manuals_btn, c["side_hover"], lambda: self.section == "manuals",
                    hover=c["side_hover2"])
        tk.Label(side, text="EMPRESAS", bg=c["side"], fg=c["side_muted"], anchor="w",
                 font=(FONT, 9, "bold")).grid(row=4, column=0, columnspan=2, sticky="ew",
                                              padx=22, pady=(0, 4))

        # Lista rolável de empresas (ScrollFrame = Canvas + Scrollbar + Frame interno)
        self.company_scroll = ScrollFrame(side, c["side"])
        self.company_scroll.grid(row=5, column=0, columnspan=2, sticky="nsew")
        self.company_inner = self.company_scroll.inner

        # Rodapé fixo: Configurações / Sistema (ações de sessão e destrutivas ficam lá)
        tk.Frame(side, bg=c["side_hover"], height=1).grid(
            row=6, column=0, columnspan=2, sticky="ew", padx=14, pady=(8, 0))
        self.settings_btn = tk.Button(
            side, text="⚙   Configurações / Sistema", anchor="w", command=self.open_settings,
            bg=c["side"], fg=c["side_fg"], activebackground=c["side_sel"],
            activeforeground="white", relief="flat", bd=0, cursor="hand2",
            font=(FONT, 11), padx=16, pady=12)
        self.settings_btn.grid(row=7, column=0, columnspan=2, sticky="ew", padx=10, pady=(6, 14))
        self._hover(self.settings_btn, c["side"], lambda: self.section == "settings")

    def _unbind_wheel_force(self):
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.unbind_all(seq)

    # ---- empresas (menu lateral) ----------------------------------------------------------
    def refresh_companies(self):
        for w in self.company_inner.winfo_children():
            w.destroy()
        self.company_buttons.clear()
        companies = self.db.list_companies()
        if not companies:
            tk.Label(self.company_inner, text="Nenhuma empresa cadastrada.", bg=COLORS["side"],
                     fg=COLORS["side_muted"], pady=20).pack(fill="x")
        for comp in companies:
            cid = comp["id"]
            b = tk.Button(self.company_inner, text=comp["nome"], anchor="w", padx=16, pady=11,
                          relief="flat", bd=0, cursor="hand2", font=(FONT, 11),
                          bg=COLORS["side"], fg=COLORS["side_fg"],
                          activebackground=COLORS["side_sel"], activeforeground="white",
                          command=lambda cid=cid: self.select_company(cid))
            b.pack(fill="x", padx=10, pady=1)
            self._hover(b, COLORS["side"],
                        lambda cid=cid: self.section == "company" and self.current_company == cid)
            self.company_buttons[cid] = b
        self._highlight()

    def _highlight(self):
        for cid, b in self.company_buttons.items():
            selected = self.section == "company" and cid == self.current_company
            b.configure(bg=COLORS["side_sel"] if selected else COLORS["side"])
        self.manuals_btn.configure(
            bg=COLORS["side_sel"] if self.section == "manuals" else COLORS["side_hover"])
        self.settings_btn.configure(
            bg=COLORS["side_sel"] if self.section == "settings" else COLORS["side"])

    def select_company(self, company_id, tab=None):
        company = self.db.get_company(company_id)
        if company is None:
            return
        self.current_company = company_id
        self.section = "company"
        self._highlight()
        self.company_view.load(company, tab)
        self.show_view("company")

    def open_settings(self):
        self.section = "settings"
        self._highlight()
        self.settings_view.refresh()
        self.show_view("settings")

    def open_manuals(self, focus_manual=None, focus_block=None):
        """Abre a Base de Conhecimento (opcionalmente já rolando até um manual/bloco)."""
        self.section = "manuals"
        self._highlight()
        self.manuals_view.refresh()
        self.show_view("manuals")
        if focus_manual is not None:
            self.after(80, lambda: self.manuals_view.focus_manual(focus_manual))
        elif focus_block is not None:
            self.after(80, lambda: self.manuals_view.focus_block(focus_block))
        else:
            self.manuals_view.scroll.canvas.yview_moveto(0)

    def companies_changed(self, removed_id=None):
        """Atualiza menu e tela de configurações (e recarrega a empresa aberta)."""
        if removed_id is not None and self.current_company == removed_id:
            self.current_company = None
        self.refresh_companies()
        self.settings_view.refresh()
        if self.current_company is not None:
            company = self.db.get_company(self.current_company)
            if company is not None:
                self.company_view.load(company)      # mantém a aba; não troca de tela

    def add_company(self):
        data = ask_form(self, "Nova empresa",
                        [{"key": "nome", "label": "Nome da empresa", "required": True}])
        if data is None:
            return
        try:
            cid = self.db.add_company(data["nome"])
        except sqlite3.IntegrityError:
            messagebox.showerror("Duplicada", f"Já existe uma empresa chamada '{data['nome']}'.")
            return
        self.refresh_companies()
        self.select_company(cid)
        self.toast("✔ Empresa criada")

    # ---- pesquisa direta --------------------------------------------------------------------
    def _search(self, term, limit=30):
        """Ativos, e-mails, manuais e blocos (nesta ordem). Cada item: (tipo, linha)."""
        results = [("asset", r) for r in self.db.search_assets(term, limit)]
        results += [("cred", r) for r in self.db.search_credentials(term, limit)]
        results += [("manual", r) for r in self.db.search_manuals(term, limit)]
        results += [("block", r) for r in self.db.search_blocks(term, limit)]
        return results

    @staticmethod
    def _result_text(kind, r):
        if kind == "asset":
            return f"[Ativo]    {r['hostname']}   |   {r['ip'] or '-'}   |   {r['empresa_nome']}"
        if kind == "cred":
            return f"[E-mail]   {r['email']}   |   {r['servico'] or '-'}   |   {r['empresa_nome']}"
        if kind == "manual":
            return f"[Manual]   {r['titulo']}   |   Bloco: {r['bloco_nome']}"
        return f"[Bloco]    {r['nome']}   |   Manuais de Apoio"

    def _on_search_key(self, event):
        if event.keysym in ("Return", "KP_Enter", "Escape", "Up", "Tab", "Left", "Right"):
            return
        if event.keysym == "Down":
            if self.search_list.winfo_ismapped():
                self.search_list.focus_set()
                self.search_list.selection_set(0)
            return
        term = self.search_var.get().strip()
        if len(term) < 2:
            self._hide_search()
            return
        self.search_results = self._search(term)
        self.search_list.delete(0, "end")
        if not self.search_results:
            self.search_list.insert("end", "Nenhum resultado")
        for kind, r in self.search_results:
            self.search_list.insert("end", self._result_text(kind, r))
        self.search_list.place(in_=self.search_entry, relx=0, rely=1.0, relwidth=1.6, y=2)
        self.search_list.lift()

    def _on_search_enter(self, _event=None):
        term = self.search_var.get().strip()
        if not term:
            return
        results = self._search(term)
        if not results:
            self.toast("Nenhum resultado encontrado", "warn")
            return
        # Correspondência exata (hostname/IP/e-mail/título) vai direto; senão, o primeiro.
        low = term.casefold()
        exact = []
        for kind, r in results:
            if kind == "asset" and (r["hostname"].casefold() == low
                                    or term in re.split(r"[,\s;]+", r["ip"] or "")):
                exact.append((kind, r))
            elif kind == "cred" and r["email"].casefold() == low:
                exact.append((kind, r))
            elif kind == "manual" and r["titulo"].casefold() == low:
                exact.append((kind, r))
            elif kind == "block" and r["nome"].casefold() == low:
                exact.append((kind, r))
        self._goto_result(*(exact or results)[0])

    def _on_search_pick(self, _event=None):
        sel = self.search_list.curselection()
        if sel and self.search_results and sel[0] < len(self.search_results):
            self._goto_result(*self.search_results[sel[0]])

    def _goto_result(self, kind, row):
        self._hide_search()
        self.search_var.set("")
        if kind == "manual":
            self.open_manuals(focus_manual=row["id"])
            return
        if kind == "block":
            self.open_manuals(focus_block=row["id"])
            return
        tab = "creds" if kind == "cred" else "assets"
        self.select_company(row["empresa_id"], tab=tab)
        panel = self.company_view.panel(tab)
        panel.refresh(select_id=row["id"])
        panel.tree.focus_set()

    def _hide_search(self):
        self.search_list.place_forget()
        self.search_results = []


def main():
    try:
        app = App()
        app.mainloop()
    except Exception:
        # Sem console (pythonw/PyInstaller): grava o erro em data/erro.log
        import traceback
        try:
            DATA_DIR.mkdir(parents=True, exist_ok=True)
            with open(ERROR_LOG, "a", encoding="utf-8") as fh:
                fh.write(traceback.format_exc() + "\n")
        except OSError:
            pass
        raise


if __name__ == "__main__":
    main()
