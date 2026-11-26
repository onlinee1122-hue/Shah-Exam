/**
 * EduPulse — Student & Admin Management Portal
 * Production-Ready CommonJS Express + MongoDB (Mongoose) + EJS Backend
 *
 * Architecture Sections:
 *  1. Dependencies & Environment Configuration
 *  2. Security Helpers, Input Validation & File Magic-Byte Verification
 *  3. Database Connection (MongoDB Atlas / Local / Dev Fallback) & GridFS
 *  4. Mongoose Schemas & Models (12 Collections with Indexes & Validation)
 *  5. Express App, Helmet, CORS, Rate Limiting, Session & CSRF Middleware
 *  6. Authentication & Authorization Middleware
 *  7. Idempotent Seed Data & Automatic Bootstrap
 *  8. REST API Routes (Auth, Dashboards, Students, Exams, Questions, Submissions,
 *     Results, Wallet, Messages, Notifications, Profile, Files, Reports)
 *  9. View Rendering, 404 & Centralized Error Handling
 * 10. Server Startup & Graceful Shutdown
 */

'use strict';

require('dotenv').config();

const crypto = require('crypto');
const path = require('path');
const express = require('express');
const mongoose = require('mongoose');
const session = require('express-session');
const connectMongo = require('connect-mongo');
const bcrypt = require('bcryptjs');
const helmet = require('helmet');
const rateLimit = require('express-rate-limit');
const cors = require('cors');
const nodemailer = require('nodemailer');
const PDFDocument = require('pdfkit');

const MongoStore = connectMongo.MongoStore || connectMongo.default || connectMongo;

// ============================================================================
// 1. ENVIRONMENT CONFIGURATION & VALIDATION
// ============================================================================

const NODE_ENV = process.env.NODE_ENV || 'development';
const IS_PRODUCTION = NODE_ENV === 'production';
const PORT = Number.parseInt(process.env.PORT || '3000', 10) || 3000;
const APP_URL = (process.env.APP_URL || '').trim();

if (IS_PRODUCTION && (!process.env.MONGODB_URI || !process.env.MONGODB_URI.trim())) {
  console.warn('[DB] MONGODB_URI is not set in production; server will use fallback storage unless configured.');
}

if (IS_PRODUCTION && (!process.env.SESSION_SECRET || process.env.SESSION_SECRET.trim().length < 16)) {
  console.warn('[Auth] SESSION_SECRET is unset; using an ephemeral cryptographic signing secret for this instance.');
}

const SESSION_SECRET =
  (process.env.SESSION_SECRET && process.env.SESSION_SECRET.trim()) ||
  crypto.randomBytes(32).toString('hex');

let memoryServerInstance = null;
let gridFsBucket = null;
let httpServer = null;
let activeSessionStore = null;
let dbMode = 'disconnected';
let dbFallbackReason = '';

// ============================================================================
// 2. SECURITY HELPERS, VALIDATION & MAGIC-BYTE FILE VERIFICATION
// ============================================================================

function cleanString(value, maxLength = 500) {
  if (typeof value !== 'string') return '';
  return value.trim().slice(0, maxLength);
}

function isValidEmail(email) {
  if (typeof email !== 'string') return false;
  return /^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(email.trim()) && email.length <= 160;
}

function isStrongPassword(password) {
  if (typeof password !== 'string') return false;
  return (
    password.length >= 8 &&
    password.length <= 128 &&
    /[A-Z]/.test(password) &&
    /[a-z]/.test(password) &&
    /[0-9]/.test(password)
  );
}

function isValidObjectId(id) {
  if (typeof id !== 'string') return false;
  if (!mongoose.Types.ObjectId.isValid(id)) return false;
  return String(new mongoose.Types.ObjectId(id)) === id;
}

function stripMongoOperators(input) {
  if (Array.isArray(input)) {
    return input.map(stripMongoOperators);
  }
  if (input && typeof input === 'object' && !(input instanceof Date)) {
    const clean = {};
    for (const [key, val] of Object.entries(input)) {
      if (key.startsWith('$') || key.includes('.')) continue;
      clean[key] = stripMongoOperators(val);
    }
    return clean;
  }
  return input;
}

function sanitizeFilename(name) {
  const base = path.basename(cleanString(name || 'file', 120));
  const safe = base.replace(/[^a-zA-Z0-9._-]/g, '_');
  return safe || `file_${Date.now()}`;
}

function escapeCsvCell(value) {
  let str = value === null || value === undefined ? '' : String(value);
  if (/^[=+\-@\t\r]/.test(str)) {
    str = `'${str}`;
  }
  if (/[",\n\r]/.test(str)) {
    return `"${str.replace(/"/g, '""')}"`;
  }
  return str;
}

function formatGrade(percentage) {
  if (percentage >= 90) return 'A+';
  if (percentage >= 80) return 'A';
  if (percentage >= 70) return 'B';
  if (percentage >= 60) return 'C';
  if (percentage >= 50) return 'D';
  return 'F';
}

const BLOCKED_EXTENSIONS = new Set([
  '.exe', '.bat', '.cmd', '.sh', '.bash', '.msi', '.dll', '.js', '.mjs', '.cjs',
  '.ts', '.html', '.htm', '.svg', '.php', '.py', '.rb', '.pl', '.jsp', '.asp',
  '.aspx', '.vbs', '.ps1', '.jar', '.scr', '.com', '.pif',
]);

const ALLOWED_IMAGE_MIMES = new Map([
  ['image/png', '.png'],
  ['image/jpeg', '.jpg'],
  ['image/gif', '.gif'],
  ['image/webp', '.webp'],
]);

const ALLOWED_DOC_MIMES = new Map([
  ['application/pdf', '.pdf'],
  ['text/plain', '.txt'],
  ['text/csv', '.csv'],
  ['application/vnd.openxmlformats-officedocument.wordprocessingml.document', '.docx'],
  ['image/png', '.png'],
  ['image/jpeg', '.jpg'],
  ['image/webp', '.webp'],
]);

function detectBufferSignature(buffer) {
  if (!Buffer.isBuffer(buffer) || buffer.length < 4) return null;

  // PNG: 89 50 4E 47 0D 0A 1A 0A
  if (
    buffer.length >= 8 &&
    buffer[0] === 0x89 && buffer[1] === 0x50 && buffer[2] === 0x4e && buffer[3] === 0x47 &&
    buffer[4] === 0x0d && buffer[5] === 0x0a && buffer[6] === 0x1a && buffer[7] === 0x0a
  ) {
    return 'image/png';
  }
  // JPEG: FF D8 FF
  if (buffer[0] === 0xff && buffer[1] === 0xd8 && buffer[2] === 0xff) {
    return 'image/jpeg';
  }
  // GIF: GIF87a / GIF89a
  if (buffer.slice(0, 6).toString('ascii') === 'GIF87a' || buffer.slice(0, 6).toString('ascii') === 'GIF89a') {
    return 'image/gif';
  }
  // WEBP: RIFF....WEBP
  if (
    buffer.length >= 12 &&
    buffer.slice(0, 4).toString('ascii') === 'RIFF' &&
    buffer.slice(8, 12).toString('ascii') === 'WEBP'
  ) {
    return 'image/webp';
  }
  // PDF: %PDF-
  if (buffer.slice(0, 5).toString('ascii') === '%PDF-') {
    return 'application/pdf';
  }
  // DOCX (ZIP PK\x03\x04)
  if (buffer[0] === 0x50 && buffer[1] === 0x4b && buffer[2] === 0x03 && buffer[3] === 0x04) {
    return 'application/vnd.openxmlformats-officedocument.wordprocessingml.document';
  }
  return null;
}

function isLikelySafeTextBuffer(buffer) {
  const sample = buffer.slice(0, Math.min(buffer.length, 4096));
  for (let i = 0; i < sample.length; i += 1) {
    const b = sample[i];
    if (b === 0) return false;
    if (b < 0x09 || (b > 0x0d && b < 0x20)) return false;
  }
  const text = sample.toString('utf8').toLowerCase();
  if (text.includes('<script') || text.includes('<iframe') || text.includes('<?php')) {
    return false;
  }
  return true;
}

function parseAndValidateBase64Upload(dataUrlOrBase64, filename, declaredMime, mode = 'document') {
  if (typeof dataUrlOrBase64 !== 'string' || !dataUrlOrBase64.trim()) {
    throw Object.assign(new Error('No file data provided.'), { status: 400 });
  }

  const safeName = sanitizeFilename(filename);
  const ext = path.extname(safeName).toLowerCase();
  if (BLOCKED_EXTENSIONS.has(ext)) {
    throw Object.assign(new Error('Executable or script file types are strictly prohibited.'), { status: 400 });
  }

  let base64Part = dataUrlOrBase64.trim();
  const dataUriMatch = base64Part.match(/^data:([^;]+);base64,(.+)$/);
  if (dataUriMatch) {
    base64Part = dataUriMatch[2];
  }

  if (!/^[A-Za-z0-9+/=\r\n]+$/.test(base64Part)) {
    throw Object.assign(new Error('Invalid Base64 file encoding.'), { status: 400 });
  }

  const buffer = Buffer.from(base64Part, 'base64');
  if (!buffer.length) {
    throw Object.assign(new Error('Uploaded file is empty.'), { status: 400 });
  }

  const maxBytes = mode === 'image' ? 250 * 1024 : 5 * 1024 * 1024;
  if (buffer.length > maxBytes) {
    const limitLabel = mode === 'image' ? '250 KB' : '5 MB';
    throw Object.assign(new Error(`File exceeds maximum allowed size of ${limitLabel}.`), { status: 413 });
  }

  const detectedMime = detectBufferSignature(buffer);
  let verifiedMime = detectedMime;

  if (!verifiedMime && mode === 'document' && (ext === '.txt' || ext === '.csv')) {
    if (!isLikelySafeTextBuffer(buffer)) {
      throw Object.assign(new Error('Text file contains unsafe or binary content.'), { status: 400 });
    }
    verifiedMime = ext === '.csv' ? 'text/csv' : 'text/plain';
  }

  const allowedMap = mode === 'image' ? ALLOWED_IMAGE_MIMES : ALLOWED_DOC_MIMES;
  if (!verifiedMime || !allowedMap.has(verifiedMime)) {
    throw Object.assign(
      new Error(
        mode === 'image'
          ? 'Unsupported image format. Please upload PNG, JPG, GIF, or WebP.'
          : 'Unsupported or unverified file content. Allowed: PDF, DOCX, TXT, CSV, PNG, JPG, WebP.'
      ),
      { status: 400 }
    );
  }

  return {
    buffer,
    size: buffer.length,
    mimeType: verifiedMime,
    safeFilename: safeName,
    dataUri: `data:${verifiedMime};base64,${buffer.toString('base64')}`,
  };
}

// ============================================================================
// 3. DATABASE CONNECTION & GRIDFS INITIALIZATION
// ============================================================================

async function connectLocalOrMemoryFallback() {
  const localUri = (process.env.LOCAL_MONGODB_URI || 'mongodb://127.0.0.1:27017/edupulse_portal').trim();
  try {
    await mongoose.connect(localUri, { serverSelectionTimeoutMS: 2000 });
    dbMode = 'local';
    console.log('[DB] Connected to local MongoDB:', localUri);
  } catch (_localErr) {
    const { MongoMemoryServer } = require('mongodb-memory-server');
    memoryServerInstance = await MongoMemoryServer.create();
    const memUri = memoryServerInstance.getUri();
    await mongoose.connect(memUri);
    dbMode = 'memory';
    console.log('[DB] Started development MongoMemoryServer instance for preview.');
  }
}

async function connectDatabase() {
  mongoose.set('strictQuery', true);

  const uri = process.env.MONGODB_URI ? process.env.MONGODB_URI.trim() : '';

  const isVercel = Boolean(process.env.VERCEL);

  if (!uri) {
    if (isVercel) {
      dbFallbackReason = 'MONGODB_URI is not configured in Vercel Environment Variables.';
      throw new Error(dbFallbackReason);
    }
    await connectLocalOrMemoryFallback();
  } else {
    const connectOpts = {
      maxPoolSize: 20,
      serverSelectionTimeoutMS: 10000,
    };
    const uriWithoutQuery = uri.split('?')[0];
    const hasDbInPath = /mongodb(?:\+srv)?:\/\/[^/]+\/[^/]+/.test(uriWithoutQuery);
    if (!hasDbInPath) {
      connectOpts.dbName = process.env.MONGODB_DB_NAME || 'edupulse_portal';
    }
    try {
      await mongoose.connect(uri, connectOpts);
      dbMode = uri.startsWith('mongodb+srv://') ? 'atlas' : 'external';
      dbFallbackReason = '';
      console.log(`[DB] Connected to MongoDB (${dbMode}, db: ${mongoose.connection.name}).`);
    } catch (err) {
      dbFallbackReason = `${err.name || 'Error'}: ${err.message}`;
      if (isVercel) {
        throw err;
      }
      console.warn(
        '[DB] Could not reach MONGODB_URI (' +
          err.message +
          '). Verify Atlas IP whitelist (0.0.0.0/0) and credentials. Falling back to local/in-memory database...'
      );
      await mongoose.disconnect().catch(() => {});
      await connectLocalOrMemoryFallback();
    }
  }

  gridFsBucket = new mongoose.mongo.GridFSBucket(mongoose.connection.db, {
    bucketName: 'portalFiles',
  });

  mongoose.connection.on('error', (err) => {
    console.error('[DB] MongoDB connection error:', err.message);
  });

  mongoose.connection.on('disconnected', () => {
    console.warn('[DB] MongoDB disconnected.');
  });
}

// ============================================================================
// 4. MONGOOSE SCHEMAS & MODELS
// ============================================================================

const userSchema = new mongoose.Schema(
  {
    name: { type: String, required: true, trim: true, minlength: 2, maxlength: 100 },
    email: { type: String, required: true, unique: true, lowercase: true, trim: true, maxlength: 160 },
    username: { type: String, unique: true, sparse: true, lowercase: true, trim: true, maxlength: 60 },
    passwordHash: { type: String, required: true, select: false },
    role: { type: String, enum: ['admin', 'student'], default: 'student', index: true },
    status: { type: String, enum: ['active', 'inactive', 'suspended'], default: 'active', index: true },
    avatarBase64: { type: String, default: '' },
    lastLoginAt: { type: Date, default: null },
    loginAttempts: { type: Number, default: 0 },
    lockUntil: { type: Date, default: null },
    passwordResetToken: { type: String, default: null, select: false },
    passwordResetExpires: { type: Date, default: null, select: false },
  },
  { timestamps: true }
);

const studentProfileSchema = new mongoose.Schema(
  {
    user: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, unique: true },
    studentId: { type: String, required: true, unique: true, trim: true, maxlength: 32 },
    phone: { type: String, trim: true, maxlength: 30, default: '' },
    address: { type: String, trim: true, maxlength: 250, default: '' },
    dateOfBirth: { type: Date, default: null },
    gender: { type: String, enum: ['Male', 'Female', 'Non-Binary', 'Prefer not to say', ''], default: '' },
    department: { type: String, trim: true, maxlength: 100, default: 'Computer Science' },
    course: { type: String, trim: true, maxlength: 120, default: '' },
    studyOption: { type: String, trim: true, maxlength: 80, default: '' },
    batchNumber: { type: String, trim: true, uppercase: true, maxlength: 60, default: 'BATCH-01', index: true },
    program: { type: String, trim: true, maxlength: 100, default: 'B.Sc. Honors' },
    semester: { type: String, trim: true, maxlength: 40, default: 'Semester 1' },
    enrollmentDate: { type: Date, default: Date.now },
    guardianName: { type: String, trim: true, maxlength: 100, default: '' },
    guardianPhone: { type: String, trim: true, maxlength: 30, default: '' },
    bio: { type: String, trim: true, maxlength: 500, default: '' },
    avatarBase64: { type: String, default: '' },
    status: { type: String, enum: ['active', 'inactive'], default: 'active', index: true },
  },
  { timestamps: true }
);

const departmentSchema = new mongoose.Schema(
  {
    name: { type: String, required: true, unique: true, trim: true, minlength: 2, maxlength: 100 },
    code: { type: String, required: true, unique: true, uppercase: true, trim: true, maxlength: 24 },
    description: { type: String, trim: true, maxlength: 500, default: '' },
    courses: [
      {
        code: { type: String, required: true, uppercase: true, trim: true, maxlength: 32 },
        title: { type: String, required: true, trim: true, maxlength: 120 },
        credits: { type: Number, min: 1, max: 20, default: 3 },
        studyOptions: [{ type: String, trim: true, maxlength: 60 }],
      },
    ],
    status: { type: String, enum: ['active', 'inactive'], default: 'active', index: true },
    createdBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null },
  },
  { timestamps: true }
);

const batchSchema = new mongoose.Schema(
  {
    batchNumber: { type: String, required: true, unique: true, uppercase: true, trim: true, minlength: 2, maxlength: 60 },
    department: { type: String, trim: true, maxlength: 100, default: '' },
    course: { type: String, trim: true, maxlength: 120, default: '' },
    studyOption: { type: String, trim: true, maxlength: 80, default: '' },
    description: { type: String, trim: true, maxlength: 300, default: '' },
    status: { type: String, enum: ['active', 'inactive'], default: 'active', index: true },
    createdBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null },
  },
  { timestamps: true }
);

const examinationSchema = new mongoose.Schema(
  {
    title: { type: String, required: true, trim: true, minlength: 3, maxlength: 160 },
    code: { type: String, required: true, unique: true, uppercase: true, trim: true, maxlength: 32 },
    department: { type: String, trim: true, maxlength: 100, default: '' },
    course: { type: String, required: true, trim: true, maxlength: 120 },
    studyOption: { type: String, trim: true, maxlength: 80, default: '' },
    batchNumber: { type: String, trim: true, uppercase: true, maxlength: 60, default: '' },
    description: { type: String, trim: true, maxlength: 2000, default: '' },
    instructions: { type: String, trim: true, maxlength: 2000, default: 'Read every question carefully before submitting.' },
    examDate: { type: Date, required: true, index: true },
    endDate: { type: Date, default: null },
    durationMinutes: { type: Number, required: true, min: 5, max: 360, default: 60 },
    totalMarks: { type: Number, required: true, min: 1, max: 1000, default: 100 },
    passingMarks: { type: Number, required: true, min: 0, max: 1000, default: 50 },
    status: { type: String, enum: ['draft', 'published', 'archived'], default: 'draft', index: true },
    assignedToAll: { type: Boolean, default: true },
    assignedStudents: [{ type: mongoose.Schema.Types.ObjectId, ref: 'User' }],
    attachmentFileId: { type: mongoose.Schema.Types.ObjectId, default: null },
    attachmentName: { type: String, default: '' },
    createdBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true },
  },
  { timestamps: true }
);

const questionSchema = new mongoose.Schema(
  {
    examination: { type: mongoose.Schema.Types.ObjectId, ref: 'Examination', required: true, index: true },
    department: { type: String, trim: true, maxlength: 100, default: '' },
    course: { type: String, trim: true, maxlength: 120, default: '' },
    studyOption: { type: String, trim: true, maxlength: 80, default: '' },
    batchNumber: { type: String, trim: true, uppercase: true, maxlength: 60, default: 'BATCH-01', index: true },
    type: { type: String, enum: ['mcq', 'true_false', 'short_answer'], required: true, default: 'mcq' },
    category: { type: String, trim: true, maxlength: 80, default: 'General' },
    prompt: { type: String, required: true, trim: true, maxlength: 2000 },
    description: { type: String, trim: true, maxlength: 1000, default: '' },
    options: [
      {
        label: { type: String, trim: true, maxlength: 10 },
        text: { type: String, trim: true, maxlength: 500 },
      },
    ],
    correctAnswer: { type: String, required: true, trim: true, maxlength: 1000 },
    marks: { type: Number, required: true, min: 1, max: 200, default: 10 },
    order: { type: Number, default: 1 },
    attachmentFileId: { type: mongoose.Schema.Types.ObjectId, default: null },
    attachmentName: { type: String, default: '' },
  },
  { timestamps: true }
);
questionSchema.index({ examination: 1, batchNumber: 1, order: 1 });

const submissionSchema = new mongoose.Schema(
  {
    examination: { type: mongoose.Schema.Types.ObjectId, ref: 'Examination', required: true },
    student: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true },
    startedAt: { type: Date, required: true, default: Date.now },
    submittedAt: { type: Date, default: null },
    status: { type: String, enum: ['in_progress', 'submitted', 'evaluated'], default: 'in_progress', index: true },
    answers: [
      {
        question: { type: mongoose.Schema.Types.ObjectId, ref: 'Question', required: true },
        answerText: { type: String, trim: true, maxlength: 4000, default: '' },
        selectedOption: { type: String, trim: true, maxlength: 200, default: '' },
        awardedMarks: { type: Number, default: 0, min: 0 },
        evaluatorNote: { type: String, trim: true, maxlength: 500, default: '' },
      },
    ],
    answerFiles: [
      {
        fileId: { type: mongoose.Schema.Types.ObjectId, required: true },
        filename: { type: String, required: true },
        mimeType: { type: String, required: true },
        size: { type: Number, required: true },
      },
    ],
    autoScore: { type: Number, default: 0 },
    manualScore: { type: Number, default: 0 },
    totalScore: { type: Number, default: 0 },
    evaluatedBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null },
    evaluatedAt: { type: Date, default: null },
  },
  { timestamps: true }
);
submissionSchema.index({ examination: 1, student: 1 }, { unique: true });

const resultSchema = new mongoose.Schema(
  {
    examination: { type: mongoose.Schema.Types.ObjectId, ref: 'Examination', required: true, index: true },
    student: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    submission: { type: mongoose.Schema.Types.ObjectId, ref: 'Submission', required: true, unique: true },
    totalMarks: { type: Number, required: true, min: 1 },
    obtainedMarks: { type: Number, required: true, min: 0 },
    percentage: { type: Number, required: true, min: 0, max: 100 },
    grade: { type: String, required: true, maxlength: 6 },
    passed: { type: Boolean, required: true },
    feedback: { type: String, trim: true, maxlength: 1500, default: '' },
    published: { type: Boolean, default: false, index: true },
    publishedAt: { type: Date, default: null },
    publishedBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null },
  },
  { timestamps: true }
);
resultSchema.index({ examination: 1, student: 1 }, { unique: true });

const walletSchema = new mongoose.Schema(
  {
    user: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, unique: true },
    balance: { type: Number, required: true, default: 0, min: 0 },
    currency: { type: String, default: 'USD', maxlength: 10 },
    status: { type: String, enum: ['active', 'frozen'], default: 'active' },
  },
  { timestamps: true }
);

const walletTransactionSchema = new mongoose.Schema(
  {
    wallet: { type: mongoose.Schema.Types.ObjectId, ref: 'Wallet', required: true, index: true },
    user: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    type: { type: String, enum: ['credit', 'debit'], required: true, index: true },
    amount: { type: Number, required: true, min: 0.01 },
    balanceBefore: { type: Number, required: true },
    balanceAfter: { type: Number, required: true },
    reference: { type: String, required: true, unique: true, trim: true },
    description: { type: String, required: true, trim: true, maxlength: 300 },
    category: {
      type: String,
      enum: ['scholarship', 'exam_fee', 'refund', 'adjustment', 'reward'],
      default: 'adjustment',
    },
    status: { type: String, enum: ['completed', 'pending', 'reversed'], default: 'completed' },
    createdBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true },
  },
  { timestamps: true }
);

const messageSchema = new mongoose.Schema(
  {
    sender: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    recipient: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    subject: { type: String, required: true, trim: true, maxlength: 180 },
    body: { type: String, required: true, trim: true, maxlength: 4000 },
    isRead: { type: Boolean, default: false, index: true },
    readAt: { type: Date, default: null },
    deletedBySender: { type: Boolean, default: false },
    deletedByRecipient: { type: Boolean, default: false },
  },
  { timestamps: true }
);

const notificationSchema = new mongoose.Schema(
  {
    user: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    type: {
      type: String,
      enum: ['exam', 'deadline', 'result', 'certificate', 'message', 'account', 'announcement'],
      default: 'announcement',
    },
    title: { type: String, required: true, trim: true, maxlength: 160 },
    message: { type: String, required: true, trim: true, maxlength: 600 },
    linkView: { type: String, default: 'dashboard' },
    isRead: { type: Boolean, default: false, index: true },
    readAt: { type: Date, default: null },
  },
  { timestamps: true }
);

const activityLogSchema = new mongoose.Schema(
  {
    actor: { type: mongoose.Schema.Types.ObjectId, ref: 'User', default: null, index: true },
    actorRole: { type: String, default: 'system' },
    action: { type: String, required: true, trim: true, maxlength: 120 },
    targetModel: { type: String, trim: true, maxlength: 60, default: '' },
    targetId: { type: String, trim: true, maxlength: 60, default: '' },
    details: { type: String, trim: true, maxlength: 500, default: '' },
    ipAddress: { type: String, default: '' },
  },
  { timestamps: true }
);

const fileMetaSchema = new mongoose.Schema(
  {
    gridFsId: { type: mongoose.Schema.Types.ObjectId, required: true, unique: true },
    uploadedBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    category: {
      type: String,
      enum: ['question_file', 'answer_file', 'exam_resource', 'lecture_file'],
      default: 'answer_file',
    },
    filename: { type: String, required: true, maxlength: 160 },
    mimeType: { type: String, required: true, maxlength: 120 },
    size: { type: Number, required: true },
    relatedExam: { type: mongoose.Schema.Types.ObjectId, ref: 'Examination', default: null },
    relatedSubmission: { type: mongoose.Schema.Types.ObjectId, ref: 'Submission', default: null },
    relatedLecture: { type: mongoose.Schema.Types.ObjectId, ref: 'Lecture', default: null },
  },
  { timestamps: true }
);

const certificateSchema = new mongoose.Schema(
  {
    certificateNumber: {
      type: String,
      required: true,
      unique: true,
      uppercase: true,
      trim: true,
      maxlength: 40,
      index: true,
    },
    student: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true, index: true },
    studentName: { type: String, required: true, trim: true, maxlength: 120 },
    studentIdCode: { type: String, trim: true, maxlength: 40, default: '' },
    department: { type: String, trim: true, maxlength: 100, default: '' },
    batchNumber: { type: String, trim: true, uppercase: true, maxlength: 60, default: 'BATCH-01' },
    examination: { type: mongoose.Schema.Types.ObjectId, ref: 'Examination', required: true, index: true },
    examTitle: { type: String, required: true, trim: true, maxlength: 180 },
    examCode: { type: String, required: true, trim: true, uppercase: true, maxlength: 40 },
    courseName: { type: String, required: true, trim: true, maxlength: 140 },
    studyOption: { type: String, trim: true, maxlength: 80, default: '' },
    submission: { type: mongoose.Schema.Types.ObjectId, ref: 'Submission', required: true, unique: true },
    obtainedMarks: { type: Number, required: true, min: 0, default: 0 },
    totalMarks: { type: Number, required: true, min: 1, default: 100 },
    percentage: { type: Number, required: true, min: 0, max: 100, default: 0 },
    grade: { type: String, required: true, maxlength: 10, default: 'F' },
    passed: { type: Boolean, default: false },
    attemptedQuestionsCount: { type: Number, min: 0, default: 0 },
    totalQuestionsCount: { type: Number, min: 0, default: 0 },
    status: { type: String, enum: ['issued', 'revoked'], default: 'issued', index: true },
    issuedAt: { type: Date, default: Date.now },
  },
  { timestamps: true }
);

const User = mongoose.model('User', userSchema);
const StudentProfile = mongoose.model('StudentProfile', studentProfileSchema);
const Department = mongoose.model('Department', departmentSchema);
const Batch = mongoose.model('Batch', batchSchema);
const Examination = mongoose.model('Examination', examinationSchema);
const Question = mongoose.model('Question', questionSchema);
const Submission = mongoose.model('Submission', submissionSchema);
const Result = mongoose.model('Result', resultSchema);
const Wallet = mongoose.model('Wallet', walletSchema);
const WalletTransaction = mongoose.model('WalletTransaction', walletTransactionSchema);
const Message = mongoose.model('Message', messageSchema);
const Notification = mongoose.model('Notification', notificationSchema);
const ActivityLog = mongoose.model('ActivityLog', activityLogSchema);
const FileMeta = mongoose.model('FileMeta', fileMetaSchema);
const Certificate = mongoose.model('Certificate', certificateSchema);
const Lecture = mongoose.model('Lecture', new mongoose.Schema(
  {
    title: { type: String, required: true, trim: true, minlength: 3, maxlength: 160 },
    code: { type: String, trim: true, uppercase: true, maxlength: 40, default: '' },
    department: { type: String, trim: true, maxlength: 100, default: 'Computer Science' },
    course: { type: String, required: true, trim: true, maxlength: 120, index: true },
    batchNumber: { type: String, required: true, trim: true, uppercase: true, maxlength: 60, default: 'BATCH-01', index: true },
    studyOption: { type: String, trim: true, maxlength: 80, default: '' },
    type: {
      type: String,
      enum: ['video_upload', 'video_link', 'pdf_document', 'reading'],
      required: true,
      default: 'video_upload',
    },
    videoUrl: { type: String, trim: true, maxlength: 1000, default: '' },
    fileMetaId: { type: mongoose.Schema.Types.ObjectId, ref: 'FileMeta', default: null },
    filename: { type: String, trim: true, maxlength: 160, default: '' },
    mimeType: { type: String, trim: true, maxlength: 120, default: '' },
    fileSize: { type: Number, default: 0 },
    description: { type: String, trim: true, maxlength: 2000, default: '' },
    durationMinutes: { type: Number, min: 1, max: 600, default: 30 },
    order: { type: Number, default: 1 },
    status: { type: String, enum: ['published', 'draft'], default: 'published', index: true },
    createdBy: { type: mongoose.Schema.Types.ObjectId, ref: 'User', required: true },
  },
  { timestamps: true }
));

// ============================================================================
// 5. EXPRESS MIDDLEWARE, SECURITY, SESSION & CSRF
// ============================================================================

const fs = require('fs');
const viewsDir = fs.existsSync(path.join(__dirname, 'views', 'index.ejs'))
  ? path.join(__dirname, 'views')
  : path.join(process.cwd(), 'views');

const app = express();
app.set('trust proxy', 1);
app.set('view engine', 'ejs');
app.set('views', viewsDir);

app.use(
  helmet({
    frameguard: false,
    crossOriginOpenerPolicy: false,
    crossOriginResourcePolicy: { policy: 'cross-origin' },
    contentSecurityPolicy: {
      directives: {
        defaultSrc: ["'self'"],
        scriptSrc: ["'self'", "'unsafe-inline'", 'https://cdn.jsdelivr.net'],
        scriptSrcAttr: ["'unsafe-inline'"],
        styleSrc: ["'self'", "'unsafe-inline'", 'https://fonts.googleapis.com', 'https://cdnjs.cloudflare.com'],
        fontSrc: ["'self'", 'https://fonts.gstatic.com', 'https://cdnjs.cloudflare.com', 'data:'],
        imgSrc: ["'self'", 'data:', 'blob:'],
        connectSrc: ["'self'", 'https://cdn.jsdelivr.net'],
        frameAncestors: [
          "'self'",
          'https://aistudio.google.com',
          'https://*.google.com',
          'https://*.googleusercontent.com',
          'https://*.usercontent.goog',
          'https://vercel.com',
        ],
      },
    },
  })
);

const VERCEL_ORIGINS = new Set(
  [
    process.env.VERCEL_URL && `https://${process.env.VERCEL_URL}`,
    process.env.VERCEL_BRANCH_URL && `https://${process.env.VERCEL_BRANCH_URL}`,
    process.env.VERCEL_PROJECT_PRODUCTION_URL && `https://${process.env.VERCEL_PROJECT_PRODUCTION_URL}`,
  ].filter(Boolean)
);

app.use(
  cors({
    origin(origin, callback) {
      if (!origin) return callback(null, true);
      if (APP_URL && origin === APP_URL) return callback(null, true);
      if (VERCEL_ORIGINS.has(origin)) return callback(null, true);
      if (/^https:\/\/ais-(dev|pre)-[a-z0-9-]+\.[a-z0-9.-]+$/.test(origin)) {
        return callback(null, true);
      }
      if (!IS_PRODUCTION && /^https?:\/\/(localhost|127\.0\.0\.1)(:\d+)?$/.test(origin)) {
        return callback(null, true);
      }
      return callback(new Error('CORS policy denied this origin.'), false);
    },
    credentials: true,
  })
);

app.use(express.json({ limit: '8mb' }));
app.use(express.urlencoded({ extended: true, limit: '8mb' }));

app.use((req, _res, next) => {
  if (req.body && typeof req.body === 'object') {
    req.body = stripMongoOperators(req.body);
  }
  if (req.query && typeof req.query === 'object') {
    req.query = stripMongoOperators(req.query);
  }
  next();
});

const authLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: 30,
  standardHeaders: true,
  legacyHeaders: false,
  message: { success: false, message: 'Too many authentication attempts. Please try again in 15 minutes.' },
});

const apiLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: 400,
  standardHeaders: true,
  legacyHeaders: false,
  message: { success: false, message: 'Rate limit exceeded. Please slow down your requests.' },
});

function configureSessionMiddleware() {
  const store = MongoStore.create({
    client: mongoose.connection.getClient(),
    collectionName: 'sessions',
    ttl: 7 * 24 * 60 * 60,
    autoRemove: 'native',
    touchAfter: 24 * 3600,
  });
  activeSessionStore = store;

  // Ensure SameSite=None cookies include Partitioned (CHIPS) for modern iframe browsers
  app.use((req, res, next) => {
    const origWriteHead = res.writeHead;
    res.writeHead = function patchedWriteHead(...args) {
      const existing = res.getHeader('Set-Cookie');
      if (existing) {
        const list = Array.isArray(existing) ? existing : [existing];
        const updated = list.map((c) => {
          const str = String(c);
          if (/SameSite=None/i.test(str) && /;\s*Secure/i.test(str) && !/;\s*Partitioned/i.test(str)) {
            return `${str}; Partitioned`;
          }
          return str;
        });
        res.setHeader('Set-Cookie', updated);
      }
      return origWriteHead.apply(this, args);
    };
    next();
  });

  app.use(
    session({
      name: 'edupulse.sid',
      secret: SESSION_SECRET,
      resave: false,
      saveUninitialized: false,
      rolling: true,
      store,
      cookie: {
        httpOnly: true,
        sameSite: 'lax',
        secure: 'auto',
        maxAge: 24 * 60 * 60 * 1000,
      },
    })
  );

  app.use((req, _res, next) => {
    if (req.session && req.session.cookie) {
      req.session.cookie.sameSite = req.secure ? 'none' : 'lax';
    }
    next();
  });

  app.use((req, _res, next) => {
    if (req.session && req.session.userId) return next();
    const bearerSid = verifyBearerToken(req.get('authorization'));
    if (!bearerSid || !activeSessionStore) return next();
    activeSessionStore.get(bearerSid, (err, sessData) => {
      if (!err && sessData && sessData.userId) {
        req.bearerSession = sessData;
        req.bearerSessionId = bearerSid;
      }
      next();
    });
  });
}

function signSessionId(sessionId) {
  return crypto.createHmac('sha256', SESSION_SECRET).update(String(sessionId)).digest('hex');
}

function createBearerToken(sessionId) {
  return `${sessionId}.${signSessionId(sessionId)}`;
}

function verifyBearerToken(authHeader) {
  if (typeof authHeader !== 'string' || !authHeader.startsWith('Bearer ')) return null;
  const token = authHeader.slice(7).trim();
  const dotIdx = token.lastIndexOf('.');
  if (dotIdx <= 0) return null;
  const sid = token.slice(0, dotIdx);
  const sig = token.slice(dotIdx + 1);
  const expected = signSessionId(sid);
  const a = Buffer.from(sig, 'utf8');
  const b = Buffer.from(expected, 'utf8');
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) return null;
  return sid;
}

function ensureSessionCsrf(req) {
  if (req.bearerSession && req.bearerSession.csrfToken) {
    return req.bearerSession.csrfToken;
  }
  if (!req.session) return '';
  if (!req.session.csrfToken) {
    req.session.csrfToken = crypto.randomBytes(32).toString('hex');
  }
  return req.session.csrfToken;
}

const PUBLIC_AUTH_CSRF_PATHS = new Set([
  '/auth/login',
  '/auth/register',
  '/auth/forgot-password',
  '/auth/reset-password',
  '/auth/setup-admin',
]);

function verifyCsrf(req, res, next) {
  const safeMethods = new Set(['GET', 'HEAD', 'OPTIONS']);
  if (safeMethods.has(req.method)) return next();

  const origin = req.get('origin');
  if (origin) {
    try {
      const originHost = new URL(origin).host.toLowerCase();
      const allowedHosts = new Set();
      const rawHost = req.get('host');
      if (rawHost) allowedHosts.add(rawHost.trim().toLowerCase());
      const rawFwdHost = req.get('x-forwarded-host');
      if (rawFwdHost) {
        for (const h of rawFwdHost.split(',')) {
          if (h.trim()) allowedHosts.add(h.trim().toLowerCase());
        }
      }
      if (APP_URL) {
        try {
          allowedHosts.add(new URL(APP_URL).host.toLowerCase());
        } catch (_e) {}
      }
      const isAiStudioHost = /^ais-(dev|pre)-[a-z0-9-]+\.[a-z0-9.-]+$/.test(originHost);
      if (allowedHosts.size > 0 && !allowedHosts.has(originHost) && !isAiStudioHost) {
        return res.status(403).json({ success: false, message: 'Invalid request origin.' });
      }
    } catch (_err) {
      return res.status(403).json({ success: false, message: 'Malformed origin header.' });
    }
  }

  const sessionToken =
    (req.session && req.session.csrfToken) ||
    (req.bearerSession && req.bearerSession.csrfToken);
  const headerToken = req.get('x-csrf-token');

  // On pre-login auth endpoints, allow initial submission when iframe cookie was blocked pre-auth
  if (PUBLIC_AUTH_CSRF_PATHS.has(req.path) && !sessionToken) {
    if (!headerToken) {
      return res.status(403).json({ success: false, message: 'Missing security token. Please refresh the page.' });
    }
    return next();
  }

  if (!sessionToken || !headerToken) {
    return res.status(403).json({ success: false, message: 'Missing security token. Please refresh the page.' });
  }

  const a = Buffer.from(String(sessionToken), 'utf8');
  const b = Buffer.from(String(headerToken), 'utf8');
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) {
    return res.status(403).json({ success: false, message: 'Security token mismatch. Please refresh and try again.' });
  }

  return next();
}

// ============================================================================
// 6. AUTHENTICATION, AUTHORIZATION & AUDIT LOG HELPERS
// ============================================================================

async function recordActivity(req, action, targetModel = '', targetId = '', details = '', explicitActor = null) {
  try {
    const actor = explicitActor || req.currentUser || null;
    await ActivityLog.create({
      actor: actor ? actor._id : null,
      actorRole: actor ? actor.role : 'system',
      action,
      targetModel,
      targetId: targetId ? String(targetId) : '',
      details: cleanString(details, 500),
      ipAddress: req ? req.ip || '' : '',
    });
  } catch (err) {
    console.error('[Audit] Failed to record activity log:', err.message);
  }
}

async function generateNextStudentId() {
  const year = new Date().getFullYear();
  const count = await StudentProfile.countDocuments();
  let seq = count + 1;
  while (true) {
    const candidate = `STU-${year}-${String(seq).padStart(4, '0')}`;
    const exists = await StudentProfile.exists({ studentId: candidate });
    if (!exists) return candidate;
    seq += 1;
  }
}

async function requireAuth(req, res, next) {
  try {
    const activeSession =
      req.session && req.session.userId ? req.session : req.bearerSession;
    if (!activeSession || !activeSession.userId) {
      return res.status(401).json({ success: false, message: 'Authentication required. Please sign in.' });
    }
    const user = await User.findById(activeSession.userId).lean();
    if (!user || user.status !== 'active') {
      if (req.session) req.session.destroy(() => {});
      if (req.bearerSessionId && activeSessionStore) {
        activeSessionStore.destroy(req.bearerSessionId, () => {});
      }
      return res.status(401).json({ success: false, message: 'Session is invalid or account is inactive.' });
    }
    req.currentUser = user;
    return next();
  } catch (err) {
    return next(err);
  }
}

function requireRole(...roles) {
  return (req, res, next) => {
    if (!req.currentUser || !roles.includes(req.currentUser.role)) {
      return res.status(403).json({ success: false, message: 'Access denied. Insufficient permissions.' });
    }
    return next();
  };
}

function regenerateAndSaveSession(req, userId, rememberMe = false) {
  return new Promise((resolve, reject) => {
    req.session.regenerate((err) => {
      if (err) return reject(err);
      req.session.userId = String(userId);
      req.session.csrfToken = crypto.randomBytes(32).toString('hex');
      req.session.cookie.sameSite = req.secure ? 'none' : 'lax';
      if (rememberMe) {
        req.session.cookie.maxAge = 7 * 24 * 60 * 60 * 1000;
      } else {
        req.session.cookie.maxAge = 24 * 60 * 60 * 1000;
      }
      req.session.save((saveErr) => {
        if (saveErr) return reject(saveErr);
        resolve({
          csrfToken: req.session.csrfToken,
          sessionToken: createBearerToken(req.sessionID),
        });
      });
    });
  });
}

// ============================================================================
// 7. IDEMPOTENT DATABASE SEEDING
// ============================================================================

async function seedInitialData() {
  const adminEmail = cleanString(process.env.SEED_ADMIN_EMAIL || '', 160).toLowerCase();
  const adminPassword = process.env.SEED_ADMIN_PASSWORD || '';
  const adminName = cleanString(process.env.SEED_ADMIN_NAME || 'System Administrator', 100);

  let adminUser = await User.findOne({ role: 'admin' });

  if (!adminUser && adminEmail && adminPassword) {
    const passwordHash = await bcrypt.hash(adminPassword, 12);
    adminUser = await User.create({
      name: adminName,
      email: adminEmail,
      username: 'admin',
      passwordHash,
      role: 'admin',
      status: 'active',
    });
    await ActivityLog.create({
      actor: adminUser._id,
      actorRole: 'admin',
      action: 'INITIAL_ADMIN_SEEDED',
      targetModel: 'User',
      targetId: String(adminUser._id),
      details: `Seeded initial administrator account (${adminUser.email})`,
    });
    console.log(`[Seed] Created initial administrator: ${adminUser.email}`);
  }

  // Idempotent department & courses seeding
  const existingDepartments = await Department.countDocuments();
  if (existingDepartments === 0) {
    await Department.insertMany([
      {
        name: 'Computer Science',
        code: 'CS',
        description: 'Software Engineering, Web Systems, and Distributed Computing',
        createdBy: adminUser ? adminUser._id : null,
        courses: [
          { code: 'CS-301', title: 'Web Systems Architecture', credits: 4, studyOptions: ['Full-Time', 'Part-Time', 'Online'] },
          { code: 'CS-204', title: 'Database Engineering', credits: 3, studyOptions: ['Full-Time', 'Hybrid', 'Evening'] },
          { code: 'CS-412', title: 'Cloud Native Systems', credits: 4, studyOptions: ['Full-Time', 'Online'] },
        ],
      },
      {
        name: 'Data Science',
        code: 'DS',
        description: 'Applied Statistics, Machine Learning, and Big Data Pipelines',
        createdBy: adminUser ? adminUser._id : null,
        courses: [
          { code: 'DS-201', title: 'Applied Analytics & Python', credits: 4, studyOptions: ['Full-Time', 'Online', 'Weekend'] },
          { code: 'DS-305', title: 'Machine Learning Foundations', credits: 4, studyOptions: ['Full-Time', 'Hybrid'] },
        ],
      },
      {
        name: 'Cybersecurity',
        code: 'SEC',
        description: 'Application Security, Cryptography, and Network Defense',
        createdBy: adminUser ? adminUser._id : null,
        courses: [
          { code: 'SEC-410', title: 'Cybersecurity Foundations', credits: 3, studyOptions: ['Full-Time', 'Evening', 'Online'] },
          { code: 'SEC-420', title: 'Ethical Hacking & PenTesting', credits: 4, studyOptions: ['Full-Time', 'Hybrid'] },
        ],
      },
      {
        name: 'Business Analytics',
        code: 'BA',
        description: 'Enterprise Intelligence, Financial Modeling, and Operations',
        createdBy: adminUser ? adminUser._id : null,
        courses: [
          { code: 'BA-110', title: 'Business Intelligence & SQL', credits: 3, studyOptions: ['Full-Time', 'Part-Time', 'Online', 'Weekend'] },
          { code: 'BA-240', title: 'Quantitative Decision Models', credits: 3, studyOptions: ['Part-Time', 'Evening'] },
        ],
      },
    ]);
  }

  // Idempotent batch seeding
  const existingBatches = await Batch.countDocuments();
  if (existingBatches === 0) {
    await Batch.insertMany([
      { batchNumber: 'BATCH-01', description: 'Primary Cohort Batch 01', status: 'active', createdBy: adminUser ? adminUser._id : null },
      { batchNumber: 'BATCH-02', description: 'Cohort Batch 02', status: 'active', createdBy: adminUser ? adminUser._id : null },
      { batchNumber: 'BATCH-03', description: 'Cohort Batch 03', status: 'active', createdBy: adminUser ? adminUser._id : null },
    ]);
  }

  // Idempotent sample students, exams, questions, results, wallet & messages
  const existingProfiles = await StudentProfile.countDocuments();
  if (existingProfiles > 0) {
    return;
  }

  const sampleStudentPassword = process.env.SEED_STUDENT_PASSWORD || '';
  const placeholderHash = sampleStudentPassword
    ? await bcrypt.hash(sampleStudentPassword, 10)
    : await bcrypt.hash(crypto.randomBytes(24).toString('hex'), 10);

  const studentSeeds = [
    {
      name: 'Maya Lin',
      email: 'maya.lin@edupulse.edu',
      username: 'maya.lin',
      studentId: 'STU-2026-0001',
      department: 'Computer Science',
      program: 'B.Sc. Software Engineering',
      semester: 'Semester 4',
      phone: '+1 (555) 204-8812',
      walletBalance: 1250,
    },
    {
      name: 'Liam OConnor',
      email: 'liam.oconnor@edupulse.edu',
      username: 'liam.oconnor',
      studentId: 'STU-2026-0002',
      department: 'Data Science',
      program: 'B.Sc. Applied Analytics',
      semester: 'Semester 3',
      phone: '+1 (555) 308-4419',
      walletBalance: 940,
    },
    {
      name: 'Sofia Patel',
      email: 'sofia.patel@edupulse.edu',
      username: 'sofia.patel',
      studentId: 'STU-2026-0003',
      department: 'Cybersecurity',
      program: 'B.Sc. Information Security',
      semester: 'Semester 5',
      phone: '+1 (555) 419-7721',
      walletBalance: 1520,
    },
    {
      name: 'Noah Mensah',
      email: 'noah.mensah@edupulse.edu',
      username: 'noah.mensah',
      studentId: 'STU-2026-0004',
      department: 'Computer Science',
      program: 'B.Sc. Artificial Intelligence',
      semester: 'Semester 2',
      phone: '+1 (555) 612-9034',
      walletBalance: 780,
    },
  ];

  const createdStudents = [];
  for (let i = 0; i < studentSeeds.length; i += 1) {
    const s = studentSeeds[i];
    let user = await User.findOne({ email: s.email });
    if (!user) {
      const enrolledAt = new Date(Date.now() - (45 - i * 9) * 24 * 60 * 60 * 1000);
      user = await User.create({
        name: s.name,
        email: s.email,
        username: s.username,
        passwordHash: placeholderHash,
        role: 'student',
        status: 'active',
        createdAt: enrolledAt,
      });
      await StudentProfile.create({
        user: user._id,
        studentId: s.studentId,
        phone: s.phone,
        department: s.department,
        program: s.program,
        semester: s.semester,
        enrollmentDate: enrolledAt,
        bio: `${s.program} student at EduPulse University.`,
        status: 'active',
      });
      const wallet = await Wallet.create({
        user: user._id,
        balance: s.walletBalance,
        currency: 'USD',
        status: 'active',
      });
      await WalletTransaction.create({
        wallet: wallet._id,
        user: user._id,
        type: 'credit',
        amount: s.walletBalance,
        balanceBefore: 0,
        balanceAfter: s.walletBalance,
        reference: `TXN-SEED-${s.studentId}`,
        description: 'Academic Merit Scholarship Disbursement',
        category: 'scholarship',
        status: 'completed',
        createdBy: adminUser ? adminUser._id : user._id,
      });
      await Notification.create({
        user: user._id,
        type: 'announcement',
        title: 'Welcome to EduPulse Portal',
        message: 'Your academic profile, wallet ledger, and upcoming examinations are ready.',
        linkView: 'dashboard',
      });
    }
    createdStudents.push(user);
  }

  const creatorId = adminUser ? adminUser._id : createdStudents[0]._id;

  const existingExams = await Examination.countDocuments();
  if (existingExams === 0) {
    const now = Date.now();
    const exam1 = await Examination.create({
      title: 'Full-Stack Web Engineering Midterm',
      code: 'CS-301-MID',
      course: 'Web Systems Architecture',
      description: 'Covers RESTful API design, HTTP security headers, session management, and relational/NoSQL modeling.',
      instructions: 'Answer all questions within 45 minutes. Multiple-choice and True/False items are auto-scored; short answers are evaluated by faculty.',
      examDate: new Date(now + 3 * 24 * 60 * 60 * 1000),
      durationMinutes: 45,
      totalMarks: 50,
      passingMarks: 25,
      status: 'published',
      assignedToAll: true,
      createdBy: creatorId,
    });

    const exam2 = await Examination.create({
      title: 'Database Systems & MongoDB Mastery',
      code: 'DB-204-FIN',
      course: 'Database Engineering',
      description: 'Assesses schema design, compound indexing, atomic updates, and aggregation workflows.',
      instructions: 'Complete all 4 questions carefully. Ensure concise technical explanations for short-answer items.',
      examDate: new Date(now + 7 * 24 * 60 * 60 * 1000),
      durationMinutes: 40,
      totalMarks: 40,
      passingMarks: 20,
      status: 'published',
      assignedToAll: true,
      createdBy: creatorId,
    });

    const exam3 = await Examination.create({
      title: 'Applied Network & Application Security',
      code: 'SEC-410-QZ',
      course: 'Cybersecurity Foundations',
      description: 'Draft examination covering CSRF defense, bcrypt password hashing, and magic-byte upload validation.',
      instructions: 'Draft assessment pending final faculty review.',
      examDate: new Date(now + 14 * 24 * 60 * 60 * 1000),
      durationMinutes: 30,
      totalMarks: 30,
      passingMarks: 18,
      status: 'draft',
      assignedToAll: true,
      createdBy: creatorId,
    });

    const q1 = await Question.create({
      examination: exam1._id,
      type: 'mcq',
      category: 'HTTP & Security',
      prompt: 'Which session cookie attribute prevents client-side JavaScript from reading the session identifier?',
      options: [
        { label: 'A', text: 'HttpOnly' },
        { label: 'B', text: 'Max-Age' },
        { label: 'C', text: 'Domain' },
        { label: 'D', text: 'Path' },
      ],
      correctAnswer: 'A',
      marks: 15,
      order: 1,
    });

    const q2 = await Question.create({
      examination: exam1._id,
      type: 'true_false',
      category: 'Authentication',
      prompt: 'Regenerating the session ID upon successful login helps mitigate session fixation attacks.',
      options: [
        { label: 'True', text: 'True' },
        { label: 'False', text: 'False' },
      ],
      correctAnswer: 'True',
      marks: 15,
      order: 2,
    });

    const q3 = await Question.create({
      examination: exam1._id,
      type: 'short_answer',
      category: 'Architecture',
      prompt: 'Explain why magic-byte validation is important when accepting user file uploads.',
      options: [],
      correctAnswer: 'Magic-byte inspection verifies actual file binary headers rather than trusting client-supplied MIME types or extensions.',
      marks: 20,
      order: 3,
    });

    await Question.insertMany([
      {
        examination: exam2._id,
        type: 'mcq',
        category: 'MongoDB',
        prompt: 'Which MongoDB operator performs an atomic numeric increment on a wallet balance field?',
        options: [
          { label: 'A', text: '$push' },
          { label: 'B', text: '$inc' },
          { label: 'C', text: '$slice' },
          { label: 'D', text: '$lookup' },
        ],
        correctAnswer: 'B',
        marks: 10,
        order: 1,
      },
      {
        examination: exam2._id,
        type: 'true_false',
        category: 'Storage',
        prompt: 'MongoDB GridFS splits large files into chunks so files exceeding the 16 MB BSON limit can be stored safely.',
        options: [
          { label: 'True', text: 'True' },
          { label: 'False', text: 'False' },
        ],
        correctAnswer: 'True',
        marks: 10,
        order: 2,
      },
      {
        examination: exam2._id,
        type: 'short_answer',
        category: 'Indexing',
        prompt: 'What is the advantage of a unique compound index on { examination: 1, student: 1 }?',
        options: [],
        correctAnswer: 'It enforces one submission per student per examination at the database level and accelerates lookups.',
        marks: 20,
        order: 3,
      },
    ]);

    await Question.create({
      examination: exam3._id,
      type: 'mcq',
      category: 'Cryptography',
      prompt: 'Which algorithm is specifically designed with adaptive work factors for password hashing?',
      options: [
        { label: 'A', text: 'MD5' },
        { label: 'B', text: 'SHA-1' },
        { label: 'C', text: 'bcrypt' },
        { label: 'D', text: 'Base64' },
      ],
      correctAnswer: 'C',
      marks: 30,
      order: 1,
    });

    // Seed sample evaluated submissions & published results for analytics
    const scores = [46, 41, 35];
    for (let i = 0; i < 3; i += 1) {
      const stu = createdStudents[i];
      const obtained = scores[i];
      const pct = Math.round((obtained / exam1.totalMarks) * 100);
      const sub = await Submission.create({
        examination: exam1._id,
        student: stu._id,
        startedAt: new Date(now - (5 - i) * 24 * 60 * 60 * 1000),
        submittedAt: new Date(now - (5 - i) * 24 * 60 * 60 * 1000 + 28 * 60 * 1000),
        status: 'evaluated',
        answers: [
          { question: q1._id, selectedOption: 'A', awardedMarks: 15, evaluatorNote: 'Correct' },
          { question: q2._id, selectedOption: 'True', awardedMarks: 15, evaluatorNote: 'Correct' },
          { question: q3._id, answerText: 'Inspecting file headers prevents spoofed MIME extensions.', awardedMarks: obtained - 30, evaluatorNote: 'Well explained.' },
        ],
        autoScore: 30,
        manualScore: obtained - 30,
        totalScore: obtained,
        evaluatedBy: creatorId,
        evaluatedAt: new Date(now - (4 - i) * 24 * 60 * 60 * 1000),
      });

      await Result.create({
        examination: exam1._id,
        student: stu._id,
        submission: sub._id,
        totalMarks: exam1.totalMarks,
        obtainedMarks: obtained,
        percentage: pct,
        grade: formatGrade(pct),
        passed: obtained >= exam1.passingMarks,
        feedback: 'Strong understanding of web application security principles.',
        published: true,
        publishedAt: new Date(now - (4 - i) * 24 * 60 * 60 * 1000),
        publishedBy: creatorId,
      });
    }

    if (adminUser) {
      await Message.create({
        sender: adminUser._id,
        recipient: createdStudents[0]._id,
        subject: 'Midterm Examination Schedule Confirmed',
        body: 'Welcome to the semester! Please review the CS-301-MID instructions in your Examinations module.',
      });
    }

    await ActivityLog.create({
      actor: creatorId,
      actorRole: adminUser ? 'admin' : 'system',
      action: 'SAMPLE_DATA_SEEDED',
      targetModel: 'System',
      details: 'Initialized sample students, examinations, questions, results, and wallet records.',
    });
  }
}

// ============================================================================
// 8. REST API ROUTES
// ============================================================================

function registerRoutes() {
  app.get('/', async (req, res, next) => {
    try {
      const csrfToken = ensureSessionCsrf(req);
      const adminCount = await User.countDocuments({ role: 'admin' });
      res.render('index', {
        appName: 'EduPulse Portal',
        csrfToken,
        needsAdminSetup: adminCount === 0,
      });
    } catch (err) {
      next(err);
    }
  });

  // Apply general rate limit and CSRF checks to /api
  app.use('/api', apiLimiter);
  app.use('/api', verifyCsrf);

  // ---------------- AUTHENTICATION ROUTES ----------------

  app.get('/api/auth/setup-status', async (req, res, next) => {
    try {
      const adminCount = await User.countDocuments({ role: 'admin' });
      const csrfToken = ensureSessionCsrf(req);
      res.json({ success: true, needsAdminSetup: adminCount === 0, csrfToken });
    } catch (err) {
      next(err);
    }
  });

  app.post('/api/auth/setup-admin', authLimiter, async (req, res, next) => {
    try {
      const existingAdmins = await User.countDocuments({ role: 'admin' });
      if (existingAdmins > 0) {
        return res.status(403).json({
          success: false,
          message: 'Initial administrator has already been configured.',
        });
      }

      const name = cleanString(req.body.name, 100);
      const email = cleanString(req.body.email, 160).toLowerCase();
      const password = typeof req.body.password === 'string' ? req.body.password : '';

      if (name.length < 2) {
        return res.status(400).json({ success: false, message: 'Administrator name must be at least 2 characters.' });
      }
      if (!isValidEmail(email)) {
        return res.status(400).json({ success: false, message: 'Please enter a valid email address.' });
      }
      if (!isStrongPassword(password)) {
        return res.status(400).json({
          success: false,
          message: 'Password must be at least 8 characters and include uppercase, lowercase, and a number.',
        });
      }

      const duplicate = await User.exists({ email });
      if (duplicate) {
        return res.status(409).json({ success: false, message: 'An account with this email already exists.' });
      }

      const passwordHash = await bcrypt.hash(password, 12);
      const admin = await User.create({
        name,
        email,
        username: email.split('@')[0],
        passwordHash,
        role: 'admin',
        status: 'active',
        lastLoginAt: new Date(),
      });

      const { csrfToken, sessionToken } = await regenerateAndSaveSession(req, admin._id, false);
      await recordActivity(req, 'ADMIN_BOOTSTRAP_CLAIMED', 'User', admin._id, `Admin setup completed for ${email}`, admin);

      return res.status(201).json({
        success: true,
        message: 'Administrator account created and signed in.',
        csrfToken,
        sessionToken,
        user: {
          id: admin._id,
          name: admin.name,
          email: admin.email,
          role: admin.role,
          status: admin.status,
        },
      });
    } catch (err) {
      return next(err);
    }
  });

  function normalizeBatchNumber(raw) {
    return cleanString(String(raw || ''), 60)
      .toUpperCase()
      .replace(/[^A-Z0-9._-]/g, '-');
  }

  async function resolveAllocatedBatch(rawBatch, fallbackBatch = 'BATCH-01') {
    const cleaned = normalizeBatchNumber(rawBatch);
    if (cleaned.length >= 2) return cleaned;
    const firstActive = await Batch.findOne({ status: 'active' }).sort({ batchNumber: 1 }).select('batchNumber').lean();
    return (firstActive && firstActive.batchNumber) || fallbackBatch;
  }

  async function getQuestionsForStudentExam(exam, studentUserId, { includeAnswerKey = false } = {}) {
    const profile = await StudentProfile.findOne({ user: studentUserId }).select('batchNumber').lean();
    const studentBatch = normalizeBatchNumber((profile && profile.batchNumber) || 'BATCH-01') || 'BATCH-01';
    const qQuery = Question.find({ examination: exam._id }).sort({ order: 1, createdAt: 1 });
    if (!includeAnswerKey) {
      qQuery.select('-correctAnswer');
    }
    const allQuestions = await qQuery.lean();

    const batchQuestions = allQuestions.filter(
      (q) => (normalizeBatchNumber(q.batchNumber || 'BATCH-01') || 'BATCH-01') === studentBatch
    );

    const examBatch = normalizeBatchNumber(exam.batchNumber || '');
    if (batchQuestions.length > 0) {
      return { studentBatch, questions: batchQuestions, eligible: true, batchMatched: true };
    }
    if (examBatch && examBatch !== studentBatch) {
      return { studentBatch, questions: [], eligible: false, batchMatched: false };
    }
    if (allQuestions.length > 0) {
      return { studentBatch, questions: [], eligible: false, batchMatched: false };
    }
    return { studentBatch, questions: [], eligible: true, batchMatched: true };
  }

  function computeEffectiveExamScale(exam, questions) {
    const qSum = (questions || []).reduce((acc, q) => acc + (Number(q.marks) || 0), 0);
    const totalMarks = qSum > 0 ? qSum : Math.max(1, Number(exam.totalMarks) || 100);
    let passingMarks = Math.max(0, Number(exam.passingMarks) || 0);
    if (qSum > 0 && exam.totalMarks > 0 && qSum !== exam.totalMarks) {
      passingMarks = Math.min(totalMarks, Math.round((passingMarks / exam.totalMarks) * totalMarks));
    }
    return { totalMarks, passingMarks };
  }

  function generateCertificateNumber() {
    const yr = new Date().getFullYear();
    const suffix = crypto.randomBytes(4).toString('hex').toUpperCase();
    return `CERT-${yr}-${suffix}`;
  }

  async function upsertCertificateForSubmission({ submission, exam, studentUser, questions = null, resultDoc = null }) {
    if (!submission || !exam || !studentUser) return null;
    const studentObjId = studentUser._id || studentUser;
    const [userDoc, profile, resolvedQuestions] = await Promise.all([
      studentUser.name ? Promise.resolve(studentUser) : User.findById(studentObjId).select('name email').lean(),
      StudentProfile.findOne({ user: studentObjId }).lean(),
      questions
        ? Promise.resolve(questions)
        : getQuestionsForStudentExam(exam, studentObjId, { includeAnswerKey: false }).then((r) => r.questions),
    ]);

    if (!userDoc) return null;

    const { totalMarks: computedTotalMarks, passingMarks: computedPassingMarks } = computeEffectiveExamScale(
      exam,
      resolvedQuestions
    );
    const totalMarks = Math.max(1, resultDoc ? resultDoc.totalMarks : computedTotalMarks);
    const obtainedMarks = Math.min(
      totalMarks,
      Math.max(0, Number(resultDoc ? resultDoc.obtainedMarks : submission.totalScore) || 0)
    );
    const percentage = Math.min(
      100,
      Math.max(0, resultDoc ? resultDoc.percentage : Math.round((obtainedMarks / totalMarks) * 100))
    );
    const grade = resultDoc ? resultDoc.grade : formatGrade(percentage);
    const passed = resultDoc ? Boolean(resultDoc.passed) : obtainedMarks >= computedPassingMarks;

    const attemptedQuestionsCount = (submission.answers || []).filter(
      (a) => (a.selectedOption && a.selectedOption.trim()) || (a.answerText && a.answerText.trim())
    ).length;

    const studentBatch = normalizeBatchNumber((profile && profile.batchNumber) || 'BATCH-01') || 'BATCH-01';
    const existing = await Certificate.findOne({ submission: submission._id });

    const fields = {
      student: studentObjId,
      studentName: userDoc.name,
      studentIdCode: (profile && profile.studentId) || '',
      department: (profile && profile.department) || exam.department || 'General Studies',
      batchNumber: studentBatch,
      examination: exam._id,
      examTitle: exam.title,
      examCode: exam.code,
      courseName: exam.course || (profile && profile.course) || 'Academic Assessment',
      studyOption: exam.studyOption || (profile && profile.studyOption) || '',
      submission: submission._id,
      obtainedMarks,
      totalMarks,
      percentage,
      grade,
      passed,
      attemptedQuestionsCount,
      totalQuestionsCount: resolvedQuestions.length || (submission.answers || []).length,
    };

    if (existing) {
      Object.assign(existing, fields);
      await existing.save();
      return { certificate: existing.toObject(), created: false };
    }

    const certificate = await Certificate.create({
      ...fields,
      certificateNumber: generateCertificateNumber(),
      status: 'issued',
      issuedAt: submission.submittedAt || new Date(),
    });

    await Notification.create({
      user: studentObjId,
      type: 'certificate',
      title: `Certificate Generated: ${certificate.certificateNumber}`,
      message: `Your certificate for ${exam.course || exam.title} (${certificate.grade} — ${certificate.percentage}%) is ready to download.`,
      linkView: 'certificates',
    });

    return { certificate: certificate.toObject(), created: true };
  }

  async function ensureCertificatesBackfilled(userFilter = {}) {
    const subFilter = { status: { $in: ['submitted', 'evaluated'] }, ...userFilter };
    const subs = await Submission.find(subFilter).lean();
    if (!subs.length) return;
    const subIds = subs.map((s) => s._id);
    const existingCerts = await Certificate.find({ submission: { $in: subIds } }).select('submission').lean();
    const existingSet = new Set(existingCerts.map((c) => String(c.submission)));
    const missingSubs = subs.filter((s) => !existingSet.has(String(s._id)));
    if (!missingSubs.length) return;

    const examIds = Array.from(new Set(missingSubs.map((s) => String(s.examination))));
    const stuIds = Array.from(new Set(missingSubs.map((s) => String(s.student))));
    const [exams, students, results] = await Promise.all([
      Examination.find({ _id: { $in: examIds } }).lean(),
      User.find({ _id: { $in: stuIds } }).select('name email').lean(),
      Result.find({ submission: { $in: missingSubs.map((s) => s._id) } }).lean(),
    ]);
    const examMap = new Map(exams.map((e) => [String(e._id), e]));
    const stuMap = new Map(students.map((u) => [String(u._id), u]));
    const resMap = new Map(results.map((r) => [String(r.submission), r]));

    for (const sub of missingSubs) {
      const exam = examMap.get(String(sub.examination));
      const studentUser = stuMap.get(String(sub.student));
      if (!exam || !studentUser) continue;
      await upsertCertificateForSubmission({
        submission: sub,
        exam,
        studentUser,
        resultDoc: resMap.get(String(sub._id)) || null,
      });
    }
  }

  function buildCertificatePdfBuffer(cert, verificationUrl) {
    return new Promise((resolve, reject) => {
      const doc = new PDFDocument({
        size: 'A4',
        layout: 'landscape',
        margins: { top: 36, bottom: 36, left: 42, right: 42 },
      });
      const chunks = [];
      doc.on('data', (chunk) => chunks.push(chunk));
      doc.on('end', () => resolve(Buffer.concat(chunks)));
      doc.on('error', reject);

      const pageW = doc.page.width;
      const pageH = doc.page.height;

      // Clean ivory background + double academic border
      doc.rect(0, 0, pageW, pageH).fill('#FCFDFE');
      doc.lineWidth(4).strokeColor('#0F5298').rect(22, 22, pageW - 44, pageH - 44).stroke();
      doc.lineWidth(1.5).strokeColor('#F39C12').rect(32, 32, pageW - 64, pageH - 64).stroke();

      // Top navy header ribbon
      doc.rect(32, 32, pageW - 64, 72).fill('#0F5298');
      doc
        .fillColor('#FFFFFF')
        .font('Helvetica-Bold')
        .fontSize(22)
        .text('EDUPULSE UNIVERSITY PORTAL', 54, 48, { width: pageW - 108, align: 'center' });
      doc
        .fillColor('#D6E8FA')
        .font('Helvetica')
        .fontSize(10.5)
        .text('OFFICIAL CERTIFICATE OF EXAMINATION & ACADEMIC ACHIEVEMENT', 54, 78, {
          width: pageW - 108,
          align: 'center',
        });

      // Certificate ID & Issue Date row
      const issuedDateStr = new Date(cert.issuedAt || cert.createdAt || Date.now()).toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'long',
        day: 'numeric',
      });
      doc.fillColor('#4F647A').font('Helvetica-Bold').fontSize(10);
      doc.text(`Certificate No: ${cert.certificateNumber}`, 54, 122, { width: 320, align: 'left' });
      doc.text(`Issued On: ${issuedDateStr}`, pageW - 374, 122, { width: 320, align: 'right' });

      // Certification Body
      doc
        .fillColor('#5F738A')
        .font('Helvetica')
        .fontSize(13)
        .text('THIS IS TO PROUDLY CERTIFY THAT', 54, 156, { width: pageW - 108, align: 'center' });

      doc
        .fillColor('#0B3C70')
        .font('Times-Bold')
        .fontSize(32)
        .text(cert.studentName || 'Student', 54, 182, { width: pageW - 108, align: 'center' });

      const metaLine = [
        cert.studentIdCode ? `Student ID: ${cert.studentIdCode}` : null,
        cert.department ? `Department: ${cert.department}` : null,
        cert.batchNumber ? `Allocated Batch: ${cert.batchNumber}` : null,
      ]
        .filter(Boolean)
        .join('   •   ');
      doc
        .fillColor('#334155')
        .font('Helvetica')
        .fontSize(11)
        .text(metaLine, 54, 224, { width: pageW - 108, align: 'center' });

      // Divider
      doc
        .moveTo(160, 250)
        .lineTo(pageW - 160, 250)
        .lineWidth(1)
        .strokeColor('#CBD5E1')
        .stroke();

      doc
        .fillColor('#475569')
        .font('Helvetica')
        .fontSize(12)
        .text('has successfully appeared in the examination requirements for the course', 54, 266, {
          width: pageW - 108,
          align: 'center',
        });

      doc
        .fillColor('#0F5298')
        .font('Helvetica-Bold')
        .fontSize(20)
        .text(cert.courseName || cert.examTitle, 54, 290, { width: pageW - 108, align: 'center' });

      const examSubtitle = `Examination: ${cert.examTitle} (${cert.examCode})${cert.studyOption ? `   •   Study Option: ${cert.studyOption}` : ''}`;
      doc
        .fillColor('#4F647A')
        .font('Helvetica')
        .fontSize(11)
        .text(examSubtitle, 54, 320, { width: pageW - 108, align: 'center' });

      // Score / Grade / Status Cards
      const cardY = 352;
      const cardW = 190;
      const gap = 26;
      const startX = (pageW - (cardW * 3 + gap * 2)) / 2;

      const metricCards = [
        { label: 'ASSESSMENT SCORE', value: `${cert.obtainedMarks} / ${cert.totalMarks} (${cert.percentage}%)`, accent: '#0F5298' },
        { label: 'AWARDED GRADE', value: `${cert.grade}`, accent: '#27AE60' },
        {
          label: 'CERTIFICATION STATUS',
          value: cert.status === 'revoked' ? 'REVOKED' : cert.passed ? 'PASSED' : 'COMPLETED',
          accent: cert.status === 'revoked' ? '#D93025' : cert.passed ? '#33B89E' : '#F39C12',
        },
      ];

      metricCards.forEach((mc, idx) => {
        const cx = startX + idx * (cardW + gap);
        doc.roundedRect(cx, cardY, cardW, 66, 6).fillAndStroke('#F4F8FC', '#D6E2EE');
        doc.rect(cx, cardY, cardW, 5).fill(mc.accent);
        doc
          .fillColor('#64748B')
          .font('Helvetica-Bold')
          .fontSize(9)
          .text(mc.label, cx + 10, cardY + 14, { width: cardW - 20, align: 'center' });
        doc
          .fillColor('#0F172A')
          .font('Helvetica-Bold')
          .fontSize(15)
          .text(mc.value, cx + 10, cardY + 33, { width: cardW - 20, align: 'center' });
      });

      // Bottom Signature & Verification Link
      const footerY = 446;
      doc
        .moveTo(64, footerY + 26)
        .lineTo(260, footerY + 26)
        .lineWidth(1)
        .strokeColor('#64748B')
        .stroke();
      doc
        .fillColor('#0F5298')
        .font('Helvetica-Bold')
        .fontSize(11)
        .text('Office of Academic Affairs', 64, footerY + 32, { width: 196, align: 'center' });
      doc
        .fillColor('#64748B')
        .font('Helvetica')
        .fontSize(9.5)
        .text('EduPulse Portal Registrar', 64, footerY + 47, { width: 196, align: 'center' });

      // Verification Box
      doc.roundedRect(310, footerY, pageW - 364, 72, 6).fillAndStroke('#EEF6FC', '#BBD6F2');
      doc
        .fillColor('#0F5298')
        .font('Helvetica-Bold')
        .fontSize(10)
        .text(`CERTIFICATE VERIFICATION LINK (Certificate No: ${cert.certificateNumber})`, 324, footerY + 11, {
          width: pageW - 392,
        });
      doc
        .fillColor('#1E293B')
        .font('Helvetica')
        .fontSize(9.5)
        .text(verificationUrl, 324, footerY + 28, { width: pageW - 392 });
      doc
        .fillColor('#475569')
        .font('Helvetica')
        .fontSize(8.5)
        .text('Open this link or enter the Certificate Number on the EduPulse Verify Certificate page to confirm authenticity.', 324, footerY + 47, {
          width: pageW - 392,
        });

      doc.end();
    });
  }

  app.post('/api/auth/register', authLimiter, async (req, res, next) => {
    try {
      const name = cleanString(req.body.name, 100);
      const email = cleanString(req.body.email, 160).toLowerCase();
      const username = cleanString(req.body.username || email.split('@')[0], 60).toLowerCase().replace(/[^a-z0-9._-]/g, '');
      const password = typeof req.body.password === 'string' ? req.body.password : '';
      const confirmPassword = typeof req.body.confirmPassword === 'string' ? req.body.confirmPassword : '';
      const department = cleanString(req.body.department || 'Computer Science', 100);
      const course = cleanString(req.body.course || '', 120);
      const studyOption = cleanString(req.body.studyOption || '', 80);
      const batchNumber = await resolveAllocatedBatch(req.body.batchNumber, 'BATCH-01');
      const phone = cleanString(req.body.phone || '', 30);

      if (name.length < 2) {
        return res.status(400).json({ success: false, message: 'Full name must be at least 2 characters.' });
      }
      if (!isValidEmail(email)) {
        return res.status(400).json({ success: false, message: 'Please provide a valid email address.' });
      }
      if (!isStrongPassword(password)) {
        return res.status(400).json({
          success: false,
          message: 'Password must be at least 8 characters with uppercase, lowercase, and a number.',
        });
      }
      if (password !== confirmPassword) {
        return res.status(400).json({ success: false, message: 'Passwords do not match.' });
      }

      const existing = await User.findOne({ $or: [{ email }, { username }] });
      if (existing) {
        return res.status(409).json({ success: false, message: 'An account with this email or username already exists.' });
      }

      const passwordHash = await bcrypt.hash(password, 12);
      const user = await User.create({
        name,
        email,
        username: username || undefined,
        passwordHash,
        role: 'student',
        status: 'active',
        lastLoginAt: new Date(),
      });

      const studentId = await generateNextStudentId();
      await StudentProfile.create({
        user: user._id,
        studentId,
        phone,
        department,
        course,
        studyOption,
        batchNumber,
        program: 'B.Sc. Honors',
        semester: 'Semester 1',
        enrollmentDate: new Date(),
        status: 'active',
      });

      const initialBonus = 250;
      const wallet = await Wallet.create({
        user: user._id,
        balance: initialBonus,
        currency: 'USD',
        status: 'active',
      });

      await WalletTransaction.create({
        wallet: wallet._id,
        user: user._id,
        type: 'credit',
        amount: initialBonus,
        balanceBefore: 0,
        balanceAfter: initialBonus,
        reference: `TXN-REG-${Date.now()}-${Math.floor(Math.random() * 1000)}`,
        description: 'New Student Orientation Wallet Credit',
        category: 'scholarship',
        status: 'completed',
        createdBy: user._id,
      });

      await Notification.create({
        user: user._id,
        type: 'account',
        title: 'Registration Confirmed',
        message: `Welcome ${name}! Your Student ID is ${studentId} and your allocated batch is ${batchNumber}.`,
        linkView: 'profile',
      });

      const { csrfToken, sessionToken } = await regenerateAndSaveSession(req, user._id, false);
      await recordActivity(req, 'STUDENT_REGISTERED', 'User', user._id, `Registered ${studentId} (${email}) in ${batchNumber}`, user);

      return res.status(201).json({
        success: true,
        message: `Registration successful! Allocated Batch: ${batchNumber}.`,
        csrfToken,
        sessionToken,
        user: {
          id: user._id,
          name: user.name,
          email: user.email,
          role: user.role,
          studentId,
          batchNumber,
        },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/auth/login', authLimiter, async (req, res, next) => {
    try {
      const identifier = cleanString(req.body.identifier || req.body.email, 160).toLowerCase();
      const password = typeof req.body.password === 'string' ? req.body.password : '';
      const rememberMe = Boolean(req.body.rememberMe);

      if (!identifier || !password) {
        return res.status(400).json({ success: false, message: 'Email/username and password are required.' });
      }

      const user = await User.findOne({
        $or: [{ email: identifier }, { username: identifier }],
      }).select('+passwordHash');

      if (!user) {
        return res.status(401).json({ success: false, message: 'Invalid credentials.' });
      }

      if (user.lockUntil && user.lockUntil > new Date()) {
        return res.status(423).json({
          success: false,
          message: 'Account temporarily locked due to repeated failed attempts. Please try again later.',
        });
      }

      if (user.status !== 'active') {
        return res.status(403).json({
          success: false,
          message: 'Your account is currently inactive. Contact an administrator.',
        });
      }

      const matches = await bcrypt.compare(password, user.passwordHash);
      if (!matches) {
        const attempts = (user.loginAttempts || 0) + 1;
        const updates = { loginAttempts: attempts };
        if (attempts >= 5) {
          updates.lockUntil = new Date(Date.now() + 15 * 60 * 1000);
          updates.loginAttempts = 0;
        }
        await User.updateOne({ _id: user._id }, { $set: updates });
        return res.status(401).json({ success: false, message: 'Invalid credentials.' });
      }

      await User.updateOne(
        { _id: user._id },
        { $set: { loginAttempts: 0, lockUntil: null, lastLoginAt: new Date() } }
      );

      const { csrfToken, sessionToken } = await regenerateAndSaveSession(req, user._id, rememberMe);
      const profile = user.role === 'student' ? await StudentProfile.findOne({ user: user._id }).lean() : null;
      await recordActivity(req, 'USER_LOGIN', 'User', user._id, `${user.role} signed in`, user);

      return res.json({
        success: true,
        message: 'Signed in successfully.',
        csrfToken,
        sessionToken,
        user: {
          id: user._id,
          name: user.name,
          email: user.email,
          role: user.role,
          studentId: profile ? profile.studentId : 'ADMIN-01',
        },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/auth/logout', (req, res) => {
    const uid =
      (req.session && req.session.userId) ||
      (req.bearerSession && req.bearerSession.userId) ||
      null;
    if (req.bearerSessionId && activeSessionStore) {
      activeSessionStore.destroy(req.bearerSessionId, () => {});
    }
    if (req.session) {
      req.session.destroy((err) => {
        res.clearCookie('edupulse.sid');
        if (err) {
          return res.status(500).json({ success: false, message: 'Could not complete logout.' });
        }
        if (uid) {
          ActivityLog.create({
            actor: uid,
            action: 'USER_LOGOUT',
            targetModel: 'User',
            targetId: uid,
            details: 'User logged out cleanly.',
          }).catch(() => {});
        }
        return res.json({ success: true, message: 'Signed out successfully.' });
      });
    } else {
      res.clearCookie('edupulse.sid');
      res.json({ success: true, message: 'Signed out.' });
    }
  });

  function getSafeResetBaseUrl(req) {
    if (APP_URL && /^https?:\/\//i.test(APP_URL)) {
      return APP_URL.replace(/\/+$/, '');
    }
    const rawHost = ((req.get('x-forwarded-host') || req.get('host') || '').split(',')[0] || '').trim().toLowerCase();
    const isAllowedHost =
      /^ais-(dev|pre)-[a-z0-9-]+\.[a-z0-9.-]+$/.test(rawHost) ||
      /^[a-z0-9-]+\.vercel\.app$/.test(rawHost) ||
      (process.env.VERCEL_PROJECT_PRODUCTION_URL && rawHost === process.env.VERCEL_PROJECT_PRODUCTION_URL.toLowerCase()) ||
      (process.env.VERCEL_URL && rawHost === process.env.VERCEL_URL.toLowerCase()) ||
      (!IS_PRODUCTION && /^(localhost|127\.0\.0\.1)(:\d+)?$/.test(rawHost));
    if (rawHost && isAllowedHost) {
      const proto = req.secure || req.get('x-forwarded-proto') === 'https' ? 'https' : 'http';
      return `${proto}://${rawHost}`;
    }
    return '';
  }

  function isSmtpConfigured() {
    const user = (process.env.SMTP_USER || '').trim();
    const pass = (process.env.SMTP_PASS || '').trim();
    const host = (process.env.SMTP_HOST || '').trim();
    const service = (process.env.SMTP_SERVICE || '').trim();
    return Boolean(user && pass && (host || service || user.toLowerCase().endsWith('@gmail.com')));
  }

  async function sendPasswordResetEmail({ to, name, resetUrl, rawToken }) {
    const user = (process.env.SMTP_USER || '').trim();
    let pass = (process.env.SMTP_PASS || '').trim();
    const host = (process.env.SMTP_HOST || '').trim() || (user.toLowerCase().endsWith('@gmail.com') ? 'smtp.gmail.com' : '');
    if ((host === 'smtp.gmail.com' || user.toLowerCase().endsWith('@gmail.com')) && /^[a-z]{4}(?:\s+[a-z]{4}){3}$/i.test(pass)) {
      pass = pass.replace(/\s+/g, '');
    }
    const service = (process.env.SMTP_SERVICE || '').trim();
    const port = Number.parseInt(process.env.SMTP_PORT || '587', 10) || 587;
    const secure = String(process.env.SMTP_SECURE || '').toLowerCase() === 'true' || port === 465;
    const from = (process.env.SMTP_FROM || '').trim() || `EduPulse Portal <${user}>`;

    const transportOpts = service
      ? { service, auth: { user, pass } }
      : { host, port, secure, auth: { user, pass } };

    const transporter = nodemailer.createTransport(transportOpts);
    const safeName = escapeBasicHtml(name || 'User');
    const safeToken = escapeBasicHtml(rawToken);
    const safeLink = resetUrl ? escapeBasicHtml(resetUrl) : '';

    const html = `
      <div style="font-family:Arial,sans-serif;max-width:560px;margin:0 auto;padding:24px;background:#F2F5F7;color:#333;">
        <div style="background:#fff;border-radius:10px;padding:24px;border-top:4px solid #0F5298;">
          <h2 style="margin:0 0 12px;color:#0F5298;">EduPulse Portal Password Reset</h2>
          <p>Hello ${safeName},</p>
          <p>We received a request to reset your EduPulse Portal password. This reset code expires in <strong>30 minutes</strong>.</p>
          ${
            safeLink
              ? `<p style="margin:20px 0;"><a href="${safeLink}" style="display:inline-block;background:#0F5298;color:#fff;text-decoration:none;padding:12px 20px;border-radius:8px;font-weight:600;">Reset Password</a></p>`
              : ''
          }
          <p style="font-size:13px;color:#555;">Or paste this reset token in the portal's Reset Password screen:</p>
          <div style="background:#F2F5F7;padding:10px 12px;border-radius:6px;font-family:monospace;font-size:13px;word-break:break-all;">${safeToken}</div>
          <p style="margin-top:18px;font-size:12px;color:#777;">If you did not request this, you can safely ignore this email.</p>
        </div>
      </div>
    `;

    const text = [
      `Hello ${name || 'User'},`,
      '',
      'We received a request to reset your EduPulse Portal password (expires in 30 minutes).',
      resetUrl ? `Reset link: ${resetUrl}` : '',
      `Reset token: ${rawToken}`,
      '',
      'If you did not request this, you can safely ignore this email.',
    ]
      .filter(Boolean)
      .join('\n');

    await transporter.sendMail({
      from,
      to,
      subject: 'EduPulse Portal — Password Reset Instructions',
      text,
      html,
    });
  }

  app.post('/api/auth/forgot-password', authLimiter, async (req, res, next) => {
    try {
      const email = cleanString(req.body.email, 160).toLowerCase();
      if (!isValidEmail(email)) {
        return res.status(400).json({ success: false, message: 'Please enter a valid email address.' });
      }

      const smtpConfigured = isSmtpConfigured();
      let deliveryAttempted = false;
      let deliverySucceeded = false;

      const user = await User.findOne({ email });
      if (user) {
        const rawToken = crypto.randomBytes(24).toString('hex');
        const tokenHash = crypto.createHash('sha256').update(rawToken).digest('hex');
        await User.updateOne(
          { _id: user._id },
          {
            $set: {
              passwordResetToken: tokenHash,
              passwordResetExpires: new Date(Date.now() + 30 * 60 * 1000),
            },
          }
        );

        if (smtpConfigured) {
          deliveryAttempted = true;
          try {
            const baseUrl = getSafeResetBaseUrl(req);
            const resetUrl = baseUrl ? `${baseUrl}/?resetToken=${encodeURIComponent(rawToken)}` : '';
            await sendPasswordResetEmail({
              to: user.email,
              name: user.name,
              resetUrl,
              rawToken,
            });
            deliverySucceeded = true;
          } catch (mailErr) {
            console.error('[Mail] Password reset email failed:', mailErr.message);
          }
        }

        const admins = await User.find({ role: 'admin', status: 'active' }).select('_id').lean();
        if (admins.length) {
          await Notification.insertMany(
            admins.map((a) => ({
              user: a._id,
              type: 'account',
              title: 'Password Assistance Requested',
              message: `Account ${user.email} requested a password reset.`,
              linkView: 'students',
            }))
          );
        }
        await recordActivity(
          req,
          'PASSWORD_RESET_REQUESTED',
          'User',
          user._id,
          `Reset requested for ${user.email} (emailSent=${deliverySucceeded})`,
          user
        );
      }

      const message = !smtpConfigured
        ? 'Email delivery is not configured on the server yet (missing SMTP_USER / SMTP_PASS). Your request was logged for portal administration.'
        : deliveryAttempted && !deliverySucceeded
          ? 'Could not deliver the reset email due to an SMTP configuration error. Your request was logged for portal administration.'
          : 'If an account matches that email, password reset instructions have been sent. Check your inbox and spam folder.';

      return res.json({
        success: true,
        emailConfigured: smtpConfigured,
        emailSent: smtpConfigured && (!deliveryAttempted || deliverySucceeded),
        message,
      });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/auth/reset-password', authLimiter, async (req, res, next) => {
    try {
      const token = cleanString(req.body.token, 160);
      const newPassword = typeof req.body.newPassword === 'string' ? req.body.newPassword : '';
      const confirmPassword = typeof req.body.confirmPassword === 'string' ? req.body.confirmPassword : '';

      if (!/^[a-f0-9]{32,128}$/i.test(token)) {
        return res.status(400).json({ success: false, message: 'Please enter a valid reset token.' });
      }
      if (!isStrongPassword(newPassword)) {
        return res.status(400).json({
          success: false,
          message: 'New password must be >= 8 characters with uppercase, lowercase, and a number.',
        });
      }
      if (newPassword !== confirmPassword) {
        return res.status(400).json({ success: false, message: 'Passwords do not match.' });
      }

      const tokenHash = crypto.createHash('sha256').update(token).digest('hex');
      const user = await User.findOne({
        passwordResetToken: tokenHash,
        passwordResetExpires: { $gt: new Date() },
      });

      if (!user) {
        return res.status(400).json({
          success: false,
          message: 'Reset token is invalid or has expired. Please request a new reset.',
        });
      }

      const passwordHash = await bcrypt.hash(newPassword, 12);
      await User.updateOne(
        { _id: user._id },
        {
          $set: {
            passwordHash,
            passwordResetToken: null,
            passwordResetExpires: null,
            loginAttempts: 0,
            lockUntil: null,
          },
        }
      );

      await recordActivity(req, 'PASSWORD_RESET_COMPLETED', 'User', user._id, `Password reset completed for ${user.email}`, user);
      return res.json({
        success: true,
        message: 'Password has been reset successfully. You can now sign in with your new password.',
      });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/auth/me', requireAuth, async (req, res, next) => {
    try {
      const user = req.currentUser;
      const [profile, unreadMessages, unreadNotifications] = await Promise.all([
        user.role === 'student' ? StudentProfile.findOne({ user: user._id }).lean() : null,
        Message.countDocuments({ recipient: user._id, isRead: false, deletedByRecipient: false }),
        Notification.countDocuments({ user: user._id, isRead: false }),
      ]);

      return res.json({
        success: true,
        csrfToken: ensureSessionCsrf(req),
        user: {
          id: user._id,
          name: user.name,
          email: user.email,
          username: user.username || '',
          role: user.role,
          status: user.status,
          avatarBase64: (profile && profile.avatarBase64) || user.avatarBase64 || '',
          studentId: profile ? profile.studentId : 'ADMIN-001',
          batchNumber: profile ? profile.batchNumber || 'BATCH-01' : '',
          profile,
          unreadMessages,
          unreadNotifications,
        },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/auth/change-password', requireAuth, async (req, res, next) => {
    try {
      const currentPassword = typeof req.body.currentPassword === 'string' ? req.body.currentPassword : '';
      const newPassword = typeof req.body.newPassword === 'string' ? req.body.newPassword : '';
      const confirmPassword = typeof req.body.confirmPassword === 'string' ? req.body.confirmPassword : '';

      if (!currentPassword || !newPassword) {
        return res.status(400).json({ success: false, message: 'Current and new passwords are required.' });
      }
      if (!isStrongPassword(newPassword)) {
        return res.status(400).json({
          success: false,
          message: 'New password must be >= 8 characters with uppercase, lowercase, and a number.',
        });
      }
      if (newPassword !== confirmPassword) {
        return res.status(400).json({ success: false, message: 'New passwords do not match.' });
      }

      const user = await User.findById(req.currentUser._id).select('+passwordHash');
      const ok = await bcrypt.compare(currentPassword, user.passwordHash);
      if (!ok) {
        return res.status(401).json({ success: false, message: 'Current password is incorrect.' });
      }

      user.passwordHash = await bcrypt.hash(newPassword, 12);
      await user.save();
      await recordActivity(req, 'PASSWORD_CHANGED', 'User', user._id, 'User updated account password');

      return res.json({ success: true, message: 'Password updated successfully.' });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- DASHBOARDS ----------------

  app.get('/api/dashboard/student', requireAuth, requireRole('student'), async (req, res, next) => {
    try {
      const uid = req.currentUser._id;
      const [
        profile,
        wallet,
        unreadMessages,
        totalInbox,
        notifications,
        exams,
        submissions,
        results,
        activities,
      ] = await Promise.all([
        StudentProfile.findOne({ user: uid }).lean(),
        Wallet.findOne({ user: uid }).lean(),
        Message.countDocuments({ recipient: uid, isRead: false, deletedByRecipient: false }),
        Message.countDocuments({ recipient: uid, deletedByRecipient: false }),
        Notification.find({ user: uid }).sort({ createdAt: -1 }).limit(6).lean(),
        Examination.find({
          status: 'published',
          $or: [{ assignedToAll: true }, { assignedStudents: uid }],
        })
          .sort({ examDate: 1 })
          .limit(6)
          .lean(),
        Submission.find({ student: uid }).lean(),
        Result.find({ student: uid, published: true })
          .populate('examination', 'title code course')
          .sort({ publishedAt: -1 })
          .limit(8)
          .lean(),
        ActivityLog.find({ actor: uid }).sort({ createdAt: -1 }).limit(8).lean(),
      ]);

      const studentBatch = normalizeBatchNumber((profile && profile.batchNumber) || 'BATCH-01') || 'BATCH-01';
      const examIds = exams.map((e) => e._id);
      const [examQs, certCount] = await Promise.all([
        Question.find({ examination: { $in: examIds } }).select('examination batchNumber').lean(),
        Certificate.countDocuments({ student: uid, status: 'issued' }),
      ]);
      const eligibleExams = exams.filter((e) => {
        const hasSub = submissions.some((s) => String(s.examination) === String(e._id));
        if (hasSub) return true;
        const qsForExam = examQs.filter((q) => String(q.examination) === String(e._id));
        const hasBatchQ = qsForExam.some(
          (q) => (normalizeBatchNumber(q.batchNumber || 'BATCH-01') || 'BATCH-01') === studentBatch
        );
        if (hasBatchQ) return true;
        const examBatch = normalizeBatchNumber(e.batchNumber || '');
        if (examBatch && examBatch !== studentBatch) return false;
        if (qsForExam.length > 0) return false;
        return true;
      });

      const completedSubs = submissions.filter((s) => s.status !== 'in_progress').length;
      const avgScore = results.length
        ? Math.round(results.reduce((acc, r) => acc + r.percentage, 0) / results.length)
        : 0;
      const passedCount = results.filter((r) => r.passed).length;

      return res.json({
        success: true,
        profile,
        stats: {
          walletBalance: wallet ? wallet.balance : 0,
          currency: wallet ? wallet.currency : 'USD',
          unreadMessages,
          totalInbox,
          availableExams: eligibleExams.length,
          completedExams: completedSubs,
          publishedResults: results.length,
          certificatesCount: certCount,
          averagePercentage: avgScore,
          passedCount,
        },
        upcomingExams: eligibleExams,
        recentResults: results,
        notifications,
        activities,
      });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/dashboard/admin', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const [
        totalStudents,
        activeStudents,
        totalExaminations,
        publishedExaminations,
        pendingSubmissions,
        publishedResults,
        totalMessages,
        walletAgg,
        recentStudents,
        recentSubmissions,
        recentActivities,
        allResults,
        txSummary,
      ] = await Promise.all([
        User.countDocuments({ role: 'student' }),
        User.countDocuments({ role: 'student', status: 'active' }),
        Examination.countDocuments(),
        Examination.countDocuments({ status: 'published' }),
        Submission.countDocuments({ status: 'submitted' }),
        Result.countDocuments({ published: true }),
        Message.countDocuments(),
        WalletTransaction.aggregate([
          { $group: { _id: '$type', total: { $sum: '$amount' }, count: { $sum: 1 } } },
        ]),
        StudentProfile.find().populate('user', 'name email status createdAt').sort({ createdAt: -1 }).limit(5).lean(),
        Submission.find({ status: { $ne: 'in_progress' } })
          .populate('student', 'name email')
          .populate('examination', 'title code totalMarks')
          .sort({ submittedAt: -1 })
          .limit(5)
          .lean(),
        ActivityLog.find().populate('actor', 'name role').sort({ createdAt: -1 }).limit(8).lean(),
        Result.find({ published: true }).populate('examination', 'title code').lean(),
        WalletTransaction.aggregate([
          {
            $group: {
              _id: { $dateToString: { format: '%Y-%m', date: '$createdAt' } },
              credits: { $sum: { $cond: [{ $eq: ['$type', 'credit'] }, '$amount', 0] } },
              debits: { $sum: { $cond: [{ $eq: ['$type', 'debit'] }, '$amount', 0] } },
            },
          },
          { $sort: { _id: 1 } },
          { $limit: 6 },
        ]),
      ]);

      const sixMonthsAgo = new Date();
      sixMonthsAgo.setMonth(sixMonthsAgo.getMonth() - 5);
      sixMonthsAgo.setDate(1);
      const regTrend = await User.aggregate([
        { $match: { role: 'student', createdAt: { $gte: sixMonthsAgo } } },
        {
          $group: {
            _id: { $dateToString: { format: '%Y-%m', date: '$createdAt' } },
            count: { $sum: 1 },
          },
        },
        { $sort: { _id: 1 } },
      ]);

      const examPerfMap = new Map();
      for (const r of allResults) {
        const label = r.examination ? r.examination.code : 'Exam';
        const cur = examPerfMap.get(label) || { totalPct: 0, count: 0, passed: 0 };
        cur.totalPct += r.percentage;
        cur.count += 1;
        if (r.passed) cur.passed += 1;
        examPerfMap.set(label, cur);
      }

      const walletSummary = { totalCredits: 0, totalDebits: 0, transactionCount: 0 };
      for (const row of walletAgg) {
        if (row._id === 'credit') walletSummary.totalCredits = row.total;
        if (row._id === 'debit') walletSummary.totalDebits = row.total;
        walletSummary.transactionCount += row.count;
      }

      return res.json({
        success: true,
        stats: {
          totalStudents,
          activeStudents,
          totalExaminations,
          publishedExaminations,
          pendingSubmissions,
          publishedResults,
          totalMessages,
          walletSummary,
        },
        charts: {
          registrationTrend: regTrend.map((r) => ({ label: r._id, count: r.count })),
          examPerformance: Array.from(examPerfMap.entries()).map(([label, v]) => ({
            label,
            avgPercentage: Math.round(v.totalPct / v.count),
            passRate: Math.round((v.passed / v.count) * 100),
          })),
          walletFlow: txSummary.map((t) => ({ label: t._id, credits: t.credits, debits: t.debits })),
          passFail: {
            passed: allResults.filter((r) => r.passed).length,
            failed: allResults.filter((r) => !r.passed).length,
          },
        },
        recentStudents,
        recentSubmissions,
        recentActivities,
      });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- STUDENTS MANAGEMENT (ADMIN) ----------------

  app.get('/api/students', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const search = cleanString(req.query.search || '', 100);
      const statusFilter = cleanString(req.query.status || '', 20);
      const departmentFilter = cleanString(req.query.department || '', 100);
      const page = Math.max(1, Number.parseInt(req.query.page || '1', 10) || 1);
      const limit = Math.min(50, Math.max(5, Number.parseInt(req.query.limit || '10', 10) || 10));

      const userMatch = { role: 'student' };
      if (statusFilter === 'active' || statusFilter === 'inactive') {
        userMatch.status = statusFilter;
      }
      if (search) {
        const regex = new RegExp(search.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'i');
        const matchingProfiles = await StudentProfile.find({ studentId: regex }).select('user').lean();
        const profileUserIds = matchingProfiles.map((p) => p.user);
        userMatch.$or = [{ name: regex }, { email: regex }, { _id: { $in: profileUserIds } }];
      }

      if (departmentFilter) {
        const deptProfiles = await StudentProfile.find({ department: departmentFilter }).select('user').lean();
        const deptIds = deptProfiles.map((p) => p.user);
        userMatch._id = userMatch._id ? { $in: deptIds } : { $in: deptIds };
      }

      const [total, users] = await Promise.all([
        User.countDocuments(userMatch),
        User.find(userMatch)
          .sort({ createdAt: -1 })
          .skip((page - 1) * limit)
          .limit(limit)
          .lean(),
      ]);

      const userIds = users.map((u) => u._id);
      const [profiles, wallets] = await Promise.all([
        StudentProfile.find({ user: { $in: userIds } }).lean(),
        Wallet.find({ user: { $in: userIds } }).lean(),
      ]);

      const profileMap = new Map(profiles.map((p) => [String(p.user), p]));
      const walletMap = new Map(wallets.map((w) => [String(w.user), w]));

      const students = users.map((u) => {
        const p = profileMap.get(String(u._id)) || {};
        const w = walletMap.get(String(u._id)) || { balance: 0, currency: 'USD' };
        return {
          id: u._id,
          name: u.name,
          email: u.email,
          status: u.status,
          createdAt: u.createdAt,
          studentId: p.studentId || '',
          department: p.department || '',
          batchNumber: p.batchNumber || 'BATCH-01',
          program: p.program || '',
          semester: p.semester || '',
          phone: p.phone || '',
          avatarBase64: p.avatarBase64 || '',
          walletBalance: w.balance || 0,
        };
      });

      return res.json({
        success: true,
        students,
        pagination: {
          page,
          limit,
          total,
          totalPages: Math.max(1, Math.ceil(total / limit)),
        },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/students', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const name = cleanString(req.body.name, 100);
      const email = cleanString(req.body.email, 160).toLowerCase();
      const password = typeof req.body.password === 'string' ? req.body.password : '';
      const department = cleanString(req.body.department || 'Computer Science', 100);
      const batchNumber = await resolveAllocatedBatch(req.body.batchNumber, 'BATCH-01');
      const program = cleanString(req.body.program || 'B.Sc. Honors', 100);
      const semester = cleanString(req.body.semester || 'Semester 1', 40);
      const phone = cleanString(req.body.phone || '', 30);
      const initialBalance = Math.max(0, Number(req.body.initialBalance) || 0);

      if (name.length < 2 || !isValidEmail(email)) {
        return res.status(400).json({ success: false, message: 'Valid name and email are required.' });
      }
      if (!isStrongPassword(password)) {
        return res.status(400).json({
          success: false,
          message: 'Password must be >= 8 characters with uppercase, lowercase, and a number.',
        });
      }

      const exists = await User.exists({ email });
      if (exists) {
        return res.status(409).json({ success: false, message: 'A user with this email already exists.' });
      }

      const passwordHash = await bcrypt.hash(password, 12);
      const user = await User.create({
        name,
        email,
        username: email.split('@')[0],
        passwordHash,
        role: 'student',
        status: 'active',
      });

      const studentId = await generateNextStudentId();
      const profile = await StudentProfile.create({
        user: user._id,
        studentId,
        department,
        batchNumber,
        program,
        semester,
        phone,
        enrollmentDate: new Date(),
        status: 'active',
      });

      await Batch.updateOne(
        { batchNumber },
        {
          $setOnInsert: {
            batchNumber,
            department,
            status: 'active',
            createdBy: req.currentUser._id,
          },
        },
        { upsert: true }
      );

      const wallet = await Wallet.create({ user: user._id, balance: initialBalance, currency: 'USD' });
      if (initialBalance > 0) {
        await WalletTransaction.create({
          wallet: wallet._id,
          user: user._id,
          type: 'credit',
          amount: initialBalance,
          balanceBefore: 0,
          balanceAfter: initialBalance,
          reference: `TXN-ADM-${Date.now()}-${Math.floor(Math.random() * 1000)}`,
          description: 'Initial Wallet Balance Provisioned by Admin',
          category: 'adjustment',
          status: 'completed',
          createdBy: req.currentUser._id,
        });
      }

      await recordActivity(req, 'ADMIN_CREATED_STUDENT', 'User', user._id, `Created student ${studentId} (${batchNumber})`);
      return res.status(201).json({
        success: true,
        message: `Student ${name} (${studentId}) registered in ${batchNumber}.`,
        student: { id: user._id, name: user.name, email: user.email, studentId: profile.studentId, batchNumber },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/students/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid student identifier.' });
      }
      const user = await User.findOne({ _id: req.params.id, role: 'student' }).lean();
      if (!user) {
        return res.status(404).json({ success: false, message: 'Student not found.' });
      }

      const [profile, wallet, transactions, submissions, results] = await Promise.all([
        StudentProfile.findOne({ user: user._id }).lean(),
        Wallet.findOne({ user: user._id }).lean(),
        WalletTransaction.find({ user: user._id }).sort({ createdAt: -1 }).limit(15).lean(),
        Submission.find({ student: user._id }).populate('examination', 'title code totalMarks').sort({ createdAt: -1 }).lean(),
        Result.find({ student: user._id }).populate('examination', 'title code').sort({ createdAt: -1 }).lean(),
      ]);

      return res.json({
        success: true,
        student: { ...user, profile, wallet, transactions, submissions, results },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/students/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid student identifier.' });
      }
      const user = await User.findOne({ _id: req.params.id, role: 'student' });
      if (!user) {
        return res.status(404).json({ success: false, message: 'Student not found.' });
      }

      const name = cleanString(req.body.name || user.name, 100);
      const status = ['active', 'inactive', 'suspended'].includes(req.body.status) ? req.body.status : user.status;
      user.name = name;
      user.status = status;
      await user.save();

      const profileUpdates = {
        phone: cleanString(req.body.phone, 30),
        department: cleanString(req.body.department, 100),
        program: cleanString(req.body.program, 100),
        semester: cleanString(req.body.semester, 40),
        address: cleanString(req.body.address, 250),
        status: status === 'active' ? 'active' : 'inactive',
      };
      if (typeof req.body.batchNumber === 'string' && normalizeBatchNumber(req.body.batchNumber).length >= 2) {
        profileUpdates.batchNumber = normalizeBatchNumber(req.body.batchNumber);
        await Batch.updateOne(
          { batchNumber: profileUpdates.batchNumber },
          {
            $setOnInsert: {
              batchNumber: profileUpdates.batchNumber,
              department: profileUpdates.department || '',
              status: 'active',
              createdBy: req.currentUser._id,
            },
          },
          { upsert: true }
        );
      }
      await StudentProfile.updateOne({ user: user._id }, { $set: profileUpdates });

      await recordActivity(req, 'ADMIN_UPDATED_STUDENT', 'User', user._id, `Updated student ${user.email} (${status})`);
      return res.json({ success: true, message: 'Student record updated.' });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/students/:id/reset-password', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid student identifier.' });
      }
      const newPassword = typeof req.body.newPassword === 'string' ? req.body.newPassword : '';
      if (!isStrongPassword(newPassword)) {
        return res.status(400).json({
          success: false,
          message: 'New password must be >= 8 characters with uppercase, lowercase, and a number.',
        });
      }

      const user = await User.findOne({ _id: req.params.id, role: 'student' });
      if (!user) {
        return res.status(404).json({ success: false, message: 'Student not found.' });
      }

      const passwordHash = await bcrypt.hash(newPassword, 12);
      await User.updateOne(
        { _id: user._id },
        {
          $set: {
            passwordHash,
            passwordResetToken: null,
            passwordResetExpires: null,
            loginAttempts: 0,
            lockUntil: null,
          },
        }
      );

      await recordActivity(req, 'ADMIN_RESET_STUDENT_PASSWORD', 'User', user._id, `Admin reset password for ${user.email}`);
      return res.json({ success: true, message: `Password updated for ${user.name}.` });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/students/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid student identifier.' });
      }
      const user = await User.findOne({ _id: req.params.id, role: 'student' });
      if (!user) {
        return res.status(404).json({ success: false, message: 'Student not found.' });
      }

      const [hasResults, hasTx] = await Promise.all([
        Result.exists({ student: user._id }),
        WalletTransaction.exists({ user: user._id }),
      ]);

      if ((hasResults || hasTx) && req.query.force !== 'true') {
        user.status = 'inactive';
        await user.save();
        await StudentProfile.updateOne({ user: user._id }, { $set: { status: 'inactive' } });
        await recordActivity(req, 'ADMIN_DEACTIVATED_STUDENT', 'User', user._id, 'Safely deactivated student with existing records');
        return res.json({
          success: true,
          archived: true,
          message: 'Student has existing academic/financial history and was safely deactivated instead of hard-deleted.',
        });
      }

      await Promise.all([
        StudentProfile.deleteOne({ user: user._id }),
        Wallet.deleteOne({ user: user._id }),
        Notification.deleteMany({ user: user._id }),
        Message.deleteMany({ $or: [{ sender: user._id }, { recipient: user._id }] }),
        User.deleteOne({ _id: user._id }),
      ]);
      await recordActivity(req, 'ADMIN_DELETED_STUDENT', 'User', user._id, `Removed student ${user.email}`);
      return res.json({ success: true, message: 'Student account removed.' });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- DEPARTMENTS & COURSES ----------------

  function normalizeCoursesInput(rawCourses) {
    if (!Array.isArray(rawCourses)) return [];
    const seenCodes = new Set();
    const cleaned = [];
    for (const item of rawCourses) {
      if (!item || typeof item !== 'object') continue;
      const title = cleanString(item.title, 120);
      const code = cleanString(item.code, 32).toUpperCase().replace(/[^A-Z0-9_-]/g, '');
      const credits = Math.min(20, Math.max(1, Number.parseInt(item.credits, 10) || 3));
      const rawOptions = Array.isArray(item.studyOptions)
        ? item.studyOptions
        : typeof item.studyOptions === 'string'
          ? item.studyOptions.split(',')
          : [];
      const studyOptions = Array.from(
        new Set(rawOptions.map((o) => cleanString(String(o), 60)).filter(Boolean))
      );
      if (!title || !code || seenCodes.has(code)) continue;
      seenCodes.add(code);
      cleaned.push({
        code,
        title,
        credits,
        studyOptions: studyOptions.length ? studyOptions : ['Full-Time'],
      });
    }
    return cleaned;
  }

  app.get('/api/departments/public', async (_req, res, next) => {
    try {
      const [departments, batches] = await Promise.all([
        Department.find({ status: 'active' }).select('name code courses').sort({ name: 1 }).lean(),
        Batch.find({ status: 'active' }).select('batchNumber department course studyOption description').sort({ batchNumber: 1 }).lean(),
      ]);
      return res.json({ success: true, departments, batches });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/departments', requireAuth, async (req, res, next) => {
    try {
      const query = req.currentUser.role === 'admin' ? {} : { status: 'active' };
      const departments = await Department.find(query).sort({ name: 1 }).lean();
      return res.json({ success: true, departments });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/departments', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const name = cleanString(req.body.name, 100);
      const code = cleanString(req.body.code, 24).toUpperCase().replace(/[^A-Z0-9_-]/g, '');
      const description = cleanString(req.body.description, 500);
      const courses = normalizeCoursesInput(req.body.courses);

      if (name.length < 2 || code.length < 2) {
        return res.status(400).json({ success: false, message: 'Department name and code (min 2 chars) are required.' });
      }
      if (!courses.length) {
        return res.status(400).json({ success: false, message: 'Add at least one course with study options for this department.' });
      }

      const duplicate = await Department.findOne({ $or: [{ name: new RegExp(`^${name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}$`, 'i') }, { code }] });
      if (duplicate) {
        return res.status(409).json({ success: false, message: 'A department with this name or code already exists.' });
      }

      const department = await Department.create({
        name,
        code,
        description,
        courses,
        status: 'active',
        createdBy: req.currentUser._id,
      });

      await recordActivity(req, 'DEPARTMENT_CREATED', 'Department', department._id, `Created department ${name} (${code}) with ${courses.length} course(s)`);
      return res.status(201).json({ success: true, message: `Department "${name}" created.`, department });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/departments/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid department ID.' });
      }
      const dept = await Department.findById(req.params.id);
      if (!dept) {
        return res.status(404).json({ success: false, message: 'Department not found.' });
      }

      const oldName = dept.name;
      const nextName = req.body.name ? cleanString(req.body.name, 100) : dept.name;
      const nextCode = req.body.code
        ? cleanString(req.body.code, 24).toUpperCase().replace(/[^A-Z0-9_-]/g, '')
        : dept.code;

      if (nextName.length < 2 || nextCode.length < 2) {
        return res.status(400).json({ success: false, message: 'Department name and code (min 2 chars) are required.' });
      }

      const duplicate = await Department.findOne({
        _id: { $ne: dept._id },
        $or: [
          { name: new RegExp(`^${nextName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}$`, 'i') },
          { code: nextCode },
        ],
      });
      if (duplicate) {
        return res.status(409).json({ success: false, message: 'Another department with this name or code already exists.' });
      }

      dept.name = nextName;
      dept.code = nextCode;
      if (typeof req.body.description === 'string') dept.description = cleanString(req.body.description, 500);
      if (['active', 'inactive'].includes(req.body.status)) dept.status = req.body.status;
      if (Array.isArray(req.body.courses)) {
        const courses = normalizeCoursesInput(req.body.courses);
        if (!courses.length) {
          return res.status(400).json({ success: false, message: 'Department must retain at least one valid course.' });
        }
        dept.courses = courses;
      }

      await dept.save();

      if (oldName !== dept.name) {
        await Promise.all([
          StudentProfile.updateMany({ department: oldName }, { $set: { department: dept.name } }),
          Examination.updateMany({ department: oldName }, { $set: { department: dept.name } }),
          Question.updateMany({ department: oldName }, { $set: { department: dept.name } }),
        ]);
      }

      await recordActivity(req, 'DEPARTMENT_UPDATED', 'Department', dept._id, `Updated department ${dept.name} (${dept.code})`);
      return res.json({ success: true, message: `Department "${dept.name}" updated.`, department: dept });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/departments/:id/courses', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid department ID.' });
      }
      const dept = await Department.findById(req.params.id);
      if (!dept) {
        return res.status(404).json({ success: false, message: 'Department not found.' });
      }

      const [course] = normalizeCoursesInput([req.body]);
      if (!course) {
        return res.status(400).json({ success: false, message: 'Valid course code, title, and study options are required.' });
      }
      if (dept.courses.some((c) => c.code === course.code || c.title.toLowerCase() === course.title.toLowerCase())) {
        return res.status(409).json({ success: false, message: 'This course code or title already exists in the department.' });
      }

      dept.courses.push(course);
      await dept.save();
      await recordActivity(req, 'COURSE_ADDED', 'Department', dept._id, `Added course ${course.code} to ${dept.name}`);
      return res.status(201).json({ success: true, message: `Course "${course.title}" added to ${dept.name}.`, department: dept });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/departments/:id/courses/:courseId', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id) || !isValidObjectId(req.params.courseId)) {
        return res.status(400).json({ success: false, message: 'Invalid identifier.' });
      }
      const dept = await Department.findById(req.params.id);
      if (!dept) {
        return res.status(404).json({ success: false, message: 'Department not found.' });
      }
      const courseDoc = dept.courses.id(req.params.courseId);
      if (!courseDoc) {
        return res.status(404).json({ success: false, message: 'Course not found in this department.' });
      }

      const [updated] = normalizeCoursesInput([req.body]);
      if (!updated) {
        return res.status(400).json({ success: false, message: 'Valid course code, title, and study options are required.' });
      }

      const duplicate = dept.courses.some(
        (c) =>
          String(c._id) !== req.params.courseId &&
          (c.code === updated.code || c.title.toLowerCase() === updated.title.toLowerCase())
      );
      if (duplicate) {
        return res.status(409).json({ success: false, message: 'Another course in this department already uses that code or title.' });
      }

      const oldTitle = courseDoc.title;
      courseDoc.code = updated.code;
      courseDoc.title = updated.title;
      courseDoc.credits = updated.credits;
      courseDoc.studyOptions = updated.studyOptions;

      await dept.save();

      if (oldTitle !== updated.title) {
        await Promise.all([
          Examination.updateMany({ course: oldTitle }, { $set: { course: updated.title } }),
          Question.updateMany({ course: oldTitle }, { $set: { course: updated.title } }),
        ]);
      }

      await recordActivity(req, 'COURSE_UPDATED', 'Department', dept._id, `Updated course ${updated.code} (${updated.title}) in ${dept.name}`);
      return res.json({ success: true, message: `Course "${updated.title}" updated.`, department: dept });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/departments/:id/courses/:courseId', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id) || !isValidObjectId(req.params.courseId)) {
        return res.status(400).json({ success: false, message: 'Invalid identifier.' });
      }
      const dept = await Department.findById(req.params.id);
      if (!dept) {
        return res.status(404).json({ success: false, message: 'Department not found.' });
      }
      dept.courses = dept.courses.filter((c) => String(c._id) !== req.params.courseId);
      await dept.save();
      return res.json({ success: true, message: 'Course removed from department.', department: dept });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/departments/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid department ID.' });
      }
      const dept = await Department.findById(req.params.id);
      if (!dept) {
        return res.status(404).json({ success: false, message: 'Department not found.' });
      }
      await Department.deleteOne({ _id: dept._id });
      await recordActivity(req, 'DEPARTMENT_DELETED', 'Department', dept._id, `Removed department ${dept.name}`);
      return res.json({ success: true, message: `Department "${dept.name}" removed.` });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- BATCH NUMBERS MANAGEMENT ----------------

  app.get('/api/batches', requireAuth, async (req, res, next) => {
    try {
      const filter = req.currentUser.role === 'admin' ? {} : { status: 'active' };
      const batches = await Batch.find(filter).sort({ batchNumber: 1 }).lean();
      return res.json({ success: true, batches });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/batches', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const batchNumber = normalizeBatchNumber(req.body.batchNumber);
      const department = cleanString(req.body.department || '', 100);
      const course = cleanString(req.body.course || '', 120);
      const studyOption = cleanString(req.body.studyOption || '', 80);
      const description = cleanString(req.body.description || '', 300);

      if (batchNumber.length < 2) {
        return res.status(400).json({ success: false, message: 'Batch number (min 2 characters) is required.' });
      }

      const duplicate = await Batch.exists({ batchNumber });
      if (duplicate) {
        return res.status(409).json({ success: false, message: `Batch "${batchNumber}" already exists.` });
      }

      const batch = await Batch.create({
        batchNumber,
        department,
        course,
        studyOption,
        description,
        status: 'active',
        createdBy: req.currentUser._id,
      });

      await recordActivity(req, 'BATCH_CREATED', 'Batch', batch._id, `Created batch ${batchNumber}${course ? ` for ${course}` : ''}`);
      return res.status(201).json({ success: true, message: `Batch "${batchNumber}" added.`, batch });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/batches/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid batch ID.' });
      }
      const batch = await Batch.findById(req.params.id);
      if (!batch) {
        return res.status(404).json({ success: false, message: 'Batch not found.' });
      }

      const oldBatchNumber = batch.batchNumber;
      const nextBatchNumber = req.body.batchNumber ? normalizeBatchNumber(req.body.batchNumber) : batch.batchNumber;
      if (nextBatchNumber.length < 2) {
        return res.status(400).json({ success: false, message: 'Batch number must be at least 2 characters.' });
      }

      const duplicate = await Batch.exists({ _id: { $ne: batch._id }, batchNumber: nextBatchNumber });
      if (duplicate) {
        return res.status(409).json({ success: false, message: `Another batch with number "${nextBatchNumber}" already exists.` });
      }

      batch.batchNumber = nextBatchNumber;
      if (typeof req.body.department === 'string') batch.department = cleanString(req.body.department, 100);
      if (typeof req.body.course === 'string') batch.course = cleanString(req.body.course, 120);
      if (typeof req.body.studyOption === 'string') batch.studyOption = cleanString(req.body.studyOption, 80);
      if (typeof req.body.description === 'string') batch.description = cleanString(req.body.description, 300);
      if (['active', 'inactive'].includes(req.body.status)) batch.status = req.body.status;

      await batch.save();

      if (oldBatchNumber !== batch.batchNumber) {
        await Promise.all([
          Examination.updateMany({ batchNumber: oldBatchNumber }, { $set: { batchNumber: batch.batchNumber } }),
          Question.updateMany({ batchNumber: oldBatchNumber }, { $set: { batchNumber: batch.batchNumber } }),
        ]);
      }

      await recordActivity(req, 'BATCH_UPDATED', 'Batch', batch._id, `Updated batch ${batch.batchNumber}`);
      return res.json({ success: true, message: `Batch "${batch.batchNumber}" updated.`, batch });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/batches/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid batch ID.' });
      }
      const batch = await Batch.findById(req.params.id);
      if (!batch) {
        return res.status(404).json({ success: false, message: 'Batch not found.' });
      }
      await Batch.deleteOne({ _id: batch._id });
      await recordActivity(req, 'BATCH_DELETED', 'Batch', batch._id, `Removed batch ${batch.batchNumber}`);
      return res.json({ success: true, message: `Batch "${batch.batchNumber}" removed.` });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- EXAMINATIONS & QUESTIONS ----------------

  app.get('/api/examinations', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      const filter = isAdmin
        ? {}
        : { status: 'published', $or: [{ assignedToAll: true }, { assignedStudents: req.currentUser._id }] };

      if (req.query.status && isAdmin && ['draft', 'published', 'archived'].includes(req.query.status)) {
        filter.status = req.query.status;
      }

      const exams = await Examination.find(filter).sort({ examDate: 1 }).lean();
      const examIds = exams.map((e) => e._id);

      const [questionCounts, allExamQuestions] = await Promise.all([
        Question.aggregate([
          { $match: { examination: { $in: examIds } } },
          { $group: { _id: '$examination', count: { $sum: 1 }, totalMarks: { $sum: '$marks' } } },
        ]),
        !isAdmin ? Question.find({ examination: { $in: examIds } }).select('examination batchNumber marks').lean() : Promise.resolve([]),
      ]);
      const qMap = new Map(questionCounts.map((q) => [String(q._id), q]));

      let subMap = new Map();
      let resMap = new Map();
      let certMap = new Map();
      let studentBatch = '';
      if (!isAdmin) {
        const [profile, subs, results, certs] = await Promise.all([
          StudentProfile.findOne({ user: req.currentUser._id }).select('batchNumber').lean(),
          Submission.find({ student: req.currentUser._id, examination: { $in: examIds } }).lean(),
          Result.find({ student: req.currentUser._id, examination: { $in: examIds }, published: true }).lean(),
          Certificate.find({ student: req.currentUser._id, examination: { $in: examIds }, status: 'issued' }).lean(),
        ]);
        studentBatch = normalizeBatchNumber((profile && profile.batchNumber) || 'BATCH-01') || 'BATCH-01';
        subMap = new Map(subs.map((s) => [String(s.examination), s]));
        resMap = new Map(results.map((r) => [String(r.examination), r]));
        certMap = new Map(certs.map((c) => [String(c.examination), c]));
      }

      let payload = exams.map((e) => {
        const qInfo = qMap.get(String(e._id)) || { count: 0, totalMarks: 0 };
        const sub = subMap.get(String(e._id));
        const r = resMap.get(String(e._id));
        const c = certMap.get(String(e._id));

        let visibleQuestionCount = qInfo.count;
        let visibleTotalMarks = qInfo.totalMarks;
        let eligibleForBatch = true;

        if (!isAdmin) {
          const examQs = allExamQuestions.filter((q) => String(q.examination) === String(e._id));
          const myBatchQs = examQs.filter(
            (q) => (normalizeBatchNumber(q.batchNumber || 'BATCH-01') || 'BATCH-01') === studentBatch
          );
          const examBatch = normalizeBatchNumber(e.batchNumber || '');
          if (myBatchQs.length > 0) {
            visibleQuestionCount = myBatchQs.length;
            visibleTotalMarks = myBatchQs.reduce((sum, q) => sum + (Number(q.marks) || 0), 0);
            eligibleForBatch = true;
          } else if (examBatch && examBatch !== studentBatch) {
            visibleQuestionCount = 0;
            eligibleForBatch = Boolean(sub);
          } else if (examQs.length > 0) {
            visibleQuestionCount = 0;
            eligibleForBatch = Boolean(sub);
          }
        }

        return {
          ...e,
          questionCount: visibleQuestionCount,
          configuredMarks: visibleTotalMarks,
          studentBatch: !isAdmin ? studentBatch : undefined,
          eligibleForBatch,
          mySubmission: sub ? { id: sub._id, status: sub.status, startedAt: sub.startedAt, submittedAt: sub.submittedAt } : null,
          myResult: r ? { id: r._id, obtainedMarks: r.obtainedMarks, percentage: r.percentage, grade: r.grade, passed: r.passed } : null,
          myCertificate: c ? { id: c._id, certificateNumber: c.certificateNumber, grade: c.grade, percentage: c.percentage } : null,
        };
      });

      if (!isAdmin) {
        payload = payload.filter((e) => e.eligibleForBatch);
      }

      return res.json({ success: true, examinations: payload, studentBatch: !isAdmin ? studentBatch : undefined });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/examinations', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const title = cleanString(req.body.title, 160);
      const code = cleanString(req.body.code, 32).toUpperCase();
      const department = cleanString(req.body.department || '', 100);
      const course = cleanString(req.body.course, 120);
      const studyOption = cleanString(req.body.studyOption || '', 80);
      const batchNumber = cleanString(req.body.batchNumber || '', 60).toUpperCase();
      const description = cleanString(req.body.description, 2000);
      const instructions = cleanString(req.body.instructions, 2000);
      const examDate = new Date(req.body.examDate);
      const durationMinutes = Number.parseInt(req.body.durationMinutes, 10) || 60;
      const totalMarks = Number.parseInt(req.body.totalMarks, 10) || 100;
      const passingMarks = Number.parseInt(req.body.passingMarks, 10) || 50;
      const status = ['draft', 'published'].includes(req.body.status) ? req.body.status : 'draft';
      const assignedToAll = req.body.assignedToAll !== false;
      const assignedStudents = Array.isArray(req.body.assignedStudents)
        ? req.body.assignedStudents.filter(isValidObjectId)
        : [];

      if (title.length < 3 || code.length < 2 || !course) {
        return res.status(400).json({ success: false, message: 'Title, code, and course are required.' });
      }
      if (Number.isNaN(examDate.getTime())) {
        return res.status(400).json({ success: false, message: 'Valid examination date is required.' });
      }
      if (passingMarks > totalMarks) {
        return res.status(400).json({ success: false, message: 'Passing marks cannot exceed total marks.' });
      }

      const duplicate = await Examination.exists({ code });
      if (duplicate) {
        return res.status(409).json({ success: false, message: 'An examination with this code already exists.' });
      }

      const exam = await Examination.create({
        title,
        code,
        department,
        course,
        studyOption,
        batchNumber,
        description,
        instructions: instructions || undefined,
        examDate,
        durationMinutes: Math.min(360, Math.max(5, durationMinutes)),
        totalMarks,
        passingMarks,
        status,
        assignedToAll,
        assignedStudents,
        createdBy: req.currentUser._id,
      });

      if (status === 'published') {
        const targetStudents = assignedToAll
          ? await User.find({ role: 'student', status: 'active' }).select('_id').lean()
          : assignedStudents.map((id) => ({ _id: id }));
        if (targetStudents.length) {
          await Notification.insertMany(
            targetStudents.map((s) => ({
              user: s._id,
              type: 'exam',
              title: `New Examination: ${code}`,
              message: `${title} is scheduled for ${examDate.toLocaleDateString()}.`,
              linkView: 'examinations',
            }))
          );
        }
      }

      if (batchNumber) {
        await Batch.updateOne(
          { batchNumber },
          {
            $setOnInsert: {
              batchNumber,
              department,
              course,
              studyOption,
              status: 'active',
              createdBy: req.currentUser._id,
            },
          },
          { upsert: true }
        );
      }

      await recordActivity(req, 'EXAM_CREATED', 'Examination', exam._id, `Created ${code}: ${title}`);
      return res.status(201).json({ success: true, message: 'Examination created.', examination: exam });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/examinations/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid examination ID.' });
      }
      const exam = await Examination.findById(req.params.id);
      if (!exam) {
        return res.status(404).json({ success: false, message: 'Examination not found.' });
      }

      const previousStatus = exam.status;
      if (req.body.title) exam.title = cleanString(req.body.title, 160);
      if (req.body.course) exam.course = cleanString(req.body.course, 120);
      if (typeof req.body.description === 'string') exam.description = cleanString(req.body.description, 2000);
      if (typeof req.body.instructions === 'string') exam.instructions = cleanString(req.body.instructions, 2000);
      if (req.body.examDate && !Number.isNaN(new Date(req.body.examDate).getTime())) {
        exam.examDate = new Date(req.body.examDate);
      }
      if (req.body.durationMinutes) exam.durationMinutes = Math.min(360, Math.max(5, Number(req.body.durationMinutes)));
      if (req.body.totalMarks) exam.totalMarks = Math.max(1, Number(req.body.totalMarks));
      if (req.body.passingMarks !== undefined) exam.passingMarks = Math.max(0, Number(req.body.passingMarks));
      if (['draft', 'published', 'archived'].includes(req.body.status)) exam.status = req.body.status;
      if (typeof req.body.assignedToAll === 'boolean') exam.assignedToAll = req.body.assignedToAll;
      if (Array.isArray(req.body.assignedStudents)) {
        exam.assignedStudents = req.body.assignedStudents.filter(isValidObjectId);
      }

      if (exam.passingMarks > exam.totalMarks) {
        return res.status(400).json({ success: false, message: 'Passing marks cannot exceed total marks.' });
      }

      await exam.save();

      if (previousStatus !== 'published' && exam.status === 'published') {
        const targets = exam.assignedToAll
          ? await User.find({ role: 'student', status: 'active' }).select('_id').lean()
          : exam.assignedStudents.map((id) => ({ _id: id }));
        if (targets.length) {
          await Notification.insertMany(
            targets.map((s) => ({
              user: s._id,
              type: 'exam',
              title: `Examination Published: ${exam.code}`,
              message: `${exam.title} is now open in your Examinations module.`,
              linkView: 'examinations',
            }))
          );
        }
      }

      await recordActivity(req, 'EXAM_UPDATED', 'Examination', exam._id, `Updated ${exam.code} (${exam.status})`);
      return res.json({ success: true, message: 'Examination updated.', examination: exam });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/examinations/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid examination ID.' });
      }
      const hasSubmissions = await Submission.exists({ examination: req.params.id });
      if (hasSubmissions) {
        await Examination.updateOne({ _id: req.params.id }, { $set: { status: 'archived' } });
        return res.json({
          success: true,
          archived: true,
          message: 'Examination has student submissions and was archived rather than permanently deleted.',
        });
      }
      await Question.deleteMany({ examination: req.params.id });
      await Examination.deleteOne({ _id: req.params.id });
      await recordActivity(req, 'EXAM_DELETED', 'Examination', req.params.id, 'Deleted examination and questions');
      return res.json({ success: true, message: 'Examination deleted.' });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/questions', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const filter = {};
      const examId = cleanString(req.query.examId || '', 60);
      if (examId && examId !== 'all') {
        if (!isValidObjectId(examId)) {
          return res.status(400).json({ success: false, message: 'Invalid examination ID.' });
        }
        filter.examination = examId;
      }
      const courseFilter = cleanString(req.query.course || '', 120);
      const batchFilter = cleanString(req.query.batchNumber || '', 60).toUpperCase();
      if (courseFilter) filter.course = courseFilter;
      if (batchFilter) filter.batchNumber = batchFilter;

      const scopeFilter = filter.examination ? { examination: filter.examination } : {};
      const [questions, scopeQuestions, allDepts, allExams, savedBatches] = await Promise.all([
        Question.find(filter)
          .populate('examination', 'code title course department')
          .sort({ batchNumber: 1, order: 1, createdAt: 1 })
          .lean(),
        Question.find(scopeFilter).select('batchNumber course').lean(),
        Department.find({}).select('name code courses').lean(),
        Examination.find({}).select('course batchNumber').lean(),
        Batch.find({ status: 'active' }).select('batchNumber').lean(),
      ]);

      const batches = Array.from(
        new Set([
          ...savedBatches.map((b) => (b.batchNumber || '').toUpperCase()).filter(Boolean),
          ...allExams.map((e) => (e.batchNumber || '').toUpperCase()).filter(Boolean),
          ...scopeQuestions.map((q) => (q.batchNumber || 'BATCH-01').toUpperCase()),
        ])
      ).sort();
      const deptCourses = allDepts.flatMap((d) => (d.courses || []).map((c) => c.title).filter(Boolean));
      const courses = Array.from(
        new Set([
          ...deptCourses,
          ...allExams.map((e) => e.course).filter(Boolean),
          ...scopeQuestions.map((q) => q.course).filter(Boolean),
        ])
      ).sort();

      return res.json({ success: true, questions, batches, courses });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/examinations/:id/questions', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid examination ID.' });
      }
      const exam = await Examination.findById(req.params.id).lean();
      if (!exam) {
        return res.status(404).json({ success: false, message: 'Examination not found.' });
      }

      const isAdmin = req.currentUser.role === 'admin';
      if (!isAdmin) {
        if (
          exam.status !== 'published' ||
          (!exam.assignedToAll && !exam.assignedStudents.some((id) => String(id) === String(req.currentUser._id)))
        ) {
          return res.status(403).json({ success: false, message: 'You are not assigned to this examination.' });
        }

        const sub = await Submission.findOne({ examination: exam._id, student: req.currentUser._id }).lean();
        if (!sub) {
          return res.status(403).json({
            success: false,
            message: 'Start the examination first to access its questions.',
          });
        }
      }

      if (!isAdmin) {
        const scoped = await getQuestionsForStudentExam(exam, req.currentUser._id, { includeAnswerKey: false });
        if (!scoped.eligible) {
          return res.status(403).json({
            success: false,
            message: `This examination has no questions allocated to your batch (${scoped.studentBatch}).`,
          });
        }
        return res.json({
          success: true,
          examination: exam,
          studentBatch: scoped.studentBatch,
          questions: scoped.questions,
          batches: [scoped.studentBatch],
          courses: [exam.course].filter(Boolean),
        });
      }

      const filter = { examination: exam._id };
      const courseFilter = cleanString(req.query.course || '', 120);
      const batchFilter = cleanString(req.query.batchNumber || '', 60).toUpperCase();
      if (courseFilter) filter.course = courseFilter;
      if (batchFilter) filter.batchNumber = batchFilter;

      const query = Question.find(filter).sort({ batchNumber: 1, order: 1, createdAt: 1 });
      const [questions, allExamQuestions, allDepts, savedBatches] = await Promise.all([
        query.lean(),
        Question.find({ examination: exam._id }).select('batchNumber course').lean(),
        Department.find({}).select('courses').lean(),
        Batch.find({ status: 'active' }).select('batchNumber').lean(),
      ]);

      const batches = Array.from(
        new Set([
          ...savedBatches.map((b) => (b.batchNumber || '').toUpperCase()).filter(Boolean),
          ...allExamQuestions.map((q) => (q.batchNumber || 'BATCH-01').toUpperCase()),
        ])
      ).sort();
      const deptCourses = allDepts.flatMap((d) => (d.courses || []).map((c) => c.title).filter(Boolean));
      const courses = Array.from(
        new Set([exam.course, ...deptCourses, ...allExamQuestions.map((q) => q.course).filter(Boolean)])
      ).sort();

      return res.json({ success: true, examination: exam, questions, batches, courses });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/examinations/:id/questions', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid examination ID.' });
      }
      const exam = await Examination.findById(req.params.id);
      if (!exam) {
        return res.status(404).json({ success: false, message: 'Examination not found.' });
      }

      const type = ['mcq', 'true_false', 'short_answer'].includes(req.body.type) ? req.body.type : 'mcq';
      const department = cleanString(req.body.department || exam.department || '', 100);
      const course = cleanString(req.body.course || exam.course || '', 120);
      const studyOption = cleanString(req.body.studyOption || exam.studyOption || '', 80);
      const batchNumber = cleanString(req.body.batchNumber || exam.batchNumber || 'BATCH-01', 60)
        .toUpperCase()
        .replace(/[^A-Z0-9._-]/g, '-');
      const category = cleanString(req.body.category || 'General', 80);
      const prompt = cleanString(req.body.prompt, 2000);
      const description = cleanString(req.body.description, 1000);
      const correctAnswer = cleanString(req.body.correctAnswer, 1000);
      const marks = Math.max(1, Number.parseInt(req.body.marks, 10) || 10);
      const order =
        Number.parseInt(req.body.order, 10) ||
        (await Question.countDocuments({ examination: exam._id, batchNumber })) + 1;

      if (!course || !batchNumber) {
        return res.status(400).json({ success: false, message: 'Selected course and batch number are required.' });
      }
      if (!prompt || !correctAnswer) {
        return res.status(400).json({ success: false, message: 'Question prompt and correct answer are required.' });
      }

      let options = [];
      if (type === 'mcq') {
        if (!Array.isArray(req.body.options) || req.body.options.length < 2) {
          return res.status(400).json({ success: false, message: 'MCQ questions require at least 2 options.' });
        }
        options = req.body.options
          .slice(0, 6)
          .map((o, idx) => ({
            label: cleanString(o.label || String.fromCharCode(65 + idx), 10),
            text: cleanString(o.text, 500),
          }))
          .filter((o) => o.text);
      } else if (type === 'true_false') {
        options = [
          { label: 'True', text: 'True' },
          { label: 'False', text: 'False' },
        ];
      }

      const attachmentFileId = isValidObjectId(req.body.attachmentFileId) ? req.body.attachmentFileId : null;
      const attachmentName = cleanString(req.body.attachmentName || '', 160);

      const question = await Question.create({
        examination: exam._id,
        department,
        course,
        studyOption,
        batchNumber,
        type,
        category,
        prompt,
        description,
        options,
        correctAnswer,
        marks,
        order,
        attachmentFileId,
        attachmentName,
      });

      await Batch.updateOne(
        { batchNumber },
        {
          $setOnInsert: {
            batchNumber,
            department,
            course,
            studyOption,
            status: 'active',
            createdBy: req.currentUser._id,
          },
        },
        { upsert: true }
      );

      await recordActivity(
        req,
        'QUESTION_CREATED',
        'Question',
        question._id,
        `Added question to ${exam.code} (${course} / ${batchNumber})`
      );
      return res.status(201).json({
        success: true,
        message: `Question saved under batch ${batchNumber}.`,
        question,
      });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/questions/:qid', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.qid)) {
        return res.status(400).json({ success: false, message: 'Invalid question ID.' });
      }
      const q = await Question.findById(req.params.qid);
      if (!q) {
        return res.status(404).json({ success: false, message: 'Question not found.' });
      }

      if (typeof req.body.department === 'string') q.department = cleanString(req.body.department, 100);
      if (typeof req.body.course === 'string' && req.body.course.trim()) q.course = cleanString(req.body.course, 120);
      if (typeof req.body.studyOption === 'string') q.studyOption = cleanString(req.body.studyOption, 80);
      if (typeof req.body.batchNumber === 'string' && req.body.batchNumber.trim()) {
        q.batchNumber = cleanString(req.body.batchNumber, 60).toUpperCase().replace(/[^A-Z0-9._-]/g, '-');
      }
      if (req.body.prompt) q.prompt = cleanString(req.body.prompt, 2000);
      if (typeof req.body.description === 'string') q.description = cleanString(req.body.description, 1000);
      if (req.body.category) q.category = cleanString(req.body.category, 80);
      if (req.body.correctAnswer) q.correctAnswer = cleanString(req.body.correctAnswer, 1000);
      if (req.body.marks) q.marks = Math.max(1, Number.parseInt(req.body.marks, 10));
      if (Array.isArray(req.body.options) && q.type === 'mcq') {
        q.options = req.body.options
          .slice(0, 6)
          .map((o, idx) => ({
            label: cleanString(o.label || String.fromCharCode(65 + idx), 10),
            text: cleanString(o.text, 500),
          }))
          .filter((o) => o.text);
      }

      await q.save();
      return res.json({ success: true, message: 'Question updated.', question: q });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/questions/:qid', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.qid)) {
        return res.status(400).json({ success: false, message: 'Invalid question ID.' });
      }
      await Question.deleteOne({ _id: req.params.qid });
      return res.json({ success: true, message: 'Question removed.' });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- SUBMISSIONS & EVALUATION ----------------

  app.post('/api/examinations/:id/start', requireAuth, requireRole('student'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid examination ID.' });
      }
      const exam = await Examination.findById(req.params.id).lean();
      if (!exam || exam.status !== 'published') {
        return res.status(404).json({ success: false, message: 'Examination not available.' });
      }
      if (!exam.assignedToAll && !exam.assignedStudents.some((id) => String(id) === String(req.currentUser._id))) {
        return res.status(403).json({ success: false, message: 'You are not assigned to this examination.' });
      }

      const scoped = await getQuestionsForStudentExam(exam, req.currentUser._id, { includeAnswerKey: false });
      if (!scoped.eligible) {
        return res.status(403).json({
          success: false,
          message: `This examination is not scheduled for your allocated batch (${scoped.studentBatch}).`,
        });
      }

      let submission = await Submission.findOne({ examination: exam._id, student: req.currentUser._id });
      if (submission && submission.status !== 'in_progress') {
        return res.status(409).json({
          success: false,
          message: 'You have already submitted this examination.',
        });
      }

      if (!submission) {
        submission = await Submission.create({
          examination: exam._id,
          student: req.currentUser._id,
          startedAt: new Date(),
          status: 'in_progress',
          answers: [],
          answerFiles: [],
        });
        await recordActivity(req, 'EXAM_STARTED', 'Examination', exam._id, `Started ${exam.code} (${scoped.studentBatch})`);
      }

      const deadlineMs = new Date(submission.startedAt).getTime() + exam.durationMinutes * 60 * 1000;
      const remainingSeconds = Math.max(0, Math.floor((deadlineMs - Date.now()) / 1000));

      return res.json({
        success: true,
        examination: exam,
        studentBatch: scoped.studentBatch,
        submission,
        questions: scoped.questions,
        remainingSeconds,
      });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/submissions/:id/draft', requireAuth, requireRole('student'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid submission ID.' });
      }
      const submission = await Submission.findOne({ _id: req.params.id, student: req.currentUser._id });
      if (!submission) {
        return res.status(404).json({ success: false, message: 'Submission not found.' });
      }
      if (submission.status !== 'in_progress') {
        return res.status(409).json({ success: false, message: 'Finalized submissions cannot be modified.' });
      }

      const incomingAnswers = Array.isArray(req.body.answers) ? req.body.answers : [];
      submission.answers = incomingAnswers
        .filter((a) => isValidObjectId(a.question))
        .map((a) => ({
          question: a.question,
          selectedOption: cleanString(a.selectedOption || '', 200),
          answerText: cleanString(a.answerText || '', 4000),
          awardedMarks: 0,
        }));

      await submission.save();
      return res.json({ success: true, message: 'Draft saved.' });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/submissions', requireAuth, requireRole('student'), async (req, res, next) => {
    try {
      const examinationId = req.body.examinationId;
      if (!isValidObjectId(examinationId)) {
        return res.status(400).json({ success: false, message: 'Invalid examination ID.' });
      }

      const [exam, submission] = await Promise.all([
        Examination.findById(examinationId).lean(),
        Submission.findOne({ examination: examinationId, student: req.currentUser._id }),
      ]);

      if (!exam || !submission) {
        return res.status(404).json({ success: false, message: 'Examination session not found.' });
      }
      if (submission.status !== 'in_progress') {
        return res.status(409).json({ success: false, message: 'Examination already submitted.' });
      }

      const scoped = await getQuestionsForStudentExam(exam, req.currentUser._id, { includeAnswerKey: true });
      const questions = scoped.questions;

      // Server-side timer validation (with 2-minute network grace period)
      const maxAllowedMs = (exam.durationMinutes + 2) * 60 * 1000;
      const elapsedMs = Date.now() - new Date(submission.startedAt).getTime();
      if (elapsedMs > maxAllowedMs) {
        // Still allow saving whatever was answered up to deadline, flag timing in log
        await recordActivity(req, 'EXAM_LATE_SUBMISSION', 'Submission', submission._id, `Submitted after duration (${exam.code})`);
      }

      const incomingAnswers = Array.isArray(req.body.answers) ? req.body.answers : [];
      const answerMap = new Map();
      for (const a of incomingAnswers) {
        if (isValidObjectId(a.question)) {
          answerMap.set(String(a.question), a);
        }
      }

      let autoScore = 0;
      let hasManualQuestions = false;
      const gradedAnswers = [];

      for (const q of questions) {
        const supplied = answerMap.get(String(q._id)) || {};
        const selectedOption = cleanString(supplied.selectedOption || '', 200);
        const answerText = cleanString(supplied.answerText || '', 4000);
        let awardedMarks = 0;

        if (q.type === 'mcq' || q.type === 'true_false') {
          if (selectedOption.toLowerCase() === String(q.correctAnswer).trim().toLowerCase()) {
            awardedMarks = q.marks;
            autoScore += q.marks;
          }
        } else {
          hasManualQuestions = true;
        }

        gradedAnswers.push({
          question: q._id,
          selectedOption,
          answerText,
          awardedMarks,
          evaluatorNote: '',
        });
      }

      if (Array.isArray(req.body.answerFiles)) {
        const validIds = req.body.answerFiles.filter(isValidObjectId);
        if (validIds.length) {
          const metas = await FileMeta.find({
            gridFsId: { $in: validIds },
            uploadedBy: req.currentUser._id,
          }).lean();
          submission.answerFiles = metas.map((m) => ({
            fileId: m.gridFsId,
            filename: m.filename,
            mimeType: m.mimeType,
            size: m.size,
          }));
        }
      }

      submission.answers = gradedAnswers;
      submission.submittedAt = new Date();
      submission.autoScore = autoScore;
      submission.manualScore = 0;
      submission.totalScore = autoScore;
      submission.status = hasManualQuestions ? 'submitted' : 'evaluated';
      await submission.save();

      // Auto-generate Certificate as soon as student appears/submits exam
      const certOutcome = await upsertCertificateForSubmission({
        submission,
        exam,
        studentUser: req.currentUser,
        questions,
      });

      // Notify admins of new submission
      const admins = await User.find({ role: 'admin', status: 'active' }).select('_id').lean();
      if (admins.length) {
        await Notification.insertMany(
          admins.map((a) => ({
            user: a._id,
            type: 'exam',
            title: `Submission Received: ${exam.code}`,
            message: `${req.currentUser.name} (${scoped.studentBatch}) submitted ${exam.title}.`,
            linkView: 'submissions',
          }))
        );
      }

      await recordActivity(
        req,
        'EXAM_SUBMITTED',
        'Submission',
        submission._id,
        `Submitted ${exam.code} (${scoped.studentBatch})${certOutcome && certOutcome.certificate ? ` • Certificate ${certOutcome.certificate.certificateNumber}` : ''}`
      );

      return res.status(201).json({
        success: true,
        message: certOutcome && certOutcome.certificate
          ? `Examination submitted! Certificate ${certOutcome.certificate.certificateNumber} is ready.`
          : 'Examination submitted successfully!',
        submission,
        certificate: certOutcome ? certOutcome.certificate : null,
      });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/submissions', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      const filter = isAdmin ? {} : { student: req.currentUser._id };
      if (req.query.status && ['in_progress', 'submitted', 'evaluated'].includes(req.query.status)) {
        filter.status = req.query.status;
      }
      if (req.query.examinationId && isValidObjectId(req.query.examinationId)) {
        filter.examination = req.query.examinationId;
      }

      const submissions = await Submission.find(filter)
        .populate('student', 'name email')
        .populate('examination', 'title code course totalMarks passingMarks')
        .sort({ submittedAt: -1, createdAt: -1 })
        .lean();

      const subIds = submissions.map((s) => s._id);
      const results = await Result.find({ submission: { $in: subIds } }).lean();
      const resMap = new Map(results.map((r) => [String(r.submission), r]));

      const enriched = submissions.map((s) => {
        const r = resMap.get(String(s._id));
        return {
          ...s,
          result: r && (isAdmin || r.published) ? r : null,
        };
      });

      return res.json({ success: true, submissions: enriched });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/submissions/:id', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid submission ID.' });
      }
      const submission = await Submission.findById(req.params.id)
        .populate('student', 'name email')
        .populate('examination', 'title code course totalMarks passingMarks')
        .lean();

      if (!submission) {
        return res.status(404).json({ success: false, message: 'Submission not found.' });
      }

      const isAdmin = req.currentUser.role === 'admin';
      if (!isAdmin && String(submission.student._id) !== String(req.currentUser._id)) {
        return res.status(403).json({ success: false, message: 'Access denied.' });
      }

      const [result, certificate] = await Promise.all([
        Result.findOne({ submission: submission._id }).lean(),
        Certificate.findOne({ submission: submission._id }).lean(),
      ]);
      const canSeeAnswerKey = isAdmin || (result && result.published);

      const scoped = await getQuestionsForStudentExam(submission.examination, submission.student._id, {
        includeAnswerKey: canSeeAnswerKey,
      });
      let questions = scoped.questions;
      if ((!questions || !questions.length) && submission.answers && submission.answers.length) {
        const ansQIds = submission.answers.map((a) => a.question).filter(Boolean);
        const qQuery = Question.find({ _id: { $in: ansQIds } }).sort({ order: 1 });
        if (!canSeeAnswerKey) qQuery.select('-correctAnswer');
        questions = await qQuery.lean();
      }

      return res.json({
        success: true,
        submission,
        questions,
        result: canSeeAnswerKey ? result : null,
        certificate: certificate || null,
      });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/submissions/:id/evaluate', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid submission ID.' });
      }
      const submission = await Submission.findById(req.params.id);
      if (!submission) {
        return res.status(404).json({ success: false, message: 'Submission not found.' });
      }

      const exam = await Examination.findById(submission.examination).lean();
      if (!exam) {
        return res.status(404).json({ success: false, message: 'Examination not found.' });
      }
      const scoped = await getQuestionsForStudentExam(exam, submission.student, { includeAnswerKey: true });
      const questions = scoped.questions.length
        ? scoped.questions
        : await Question.find({ examination: submission.examination }).lean();

      const qMap = new Map(questions.map((q) => [String(q._id), q]));
      const marksInput = Array.isArray(req.body.marks) ? req.body.marks : [];
      const markMap = new Map(marksInput.map((m) => [String(m.question), m]));

      let autoScore = 0;
      let manualScore = 0;

      submission.answers = submission.answers.map((ans) => {
        const q = qMap.get(String(ans.question));
        const input = markMap.get(String(ans.question));
        let awarded = ans.awardedMarks || 0;
        let note = ans.evaluatorNote || '';

        if (input && input.awardedMarks !== undefined) {
          const maxQ = q ? q.marks : 1000;
          awarded = Math.min(maxQ, Math.max(0, Number(input.awardedMarks) || 0));
        }
        if (input && typeof input.evaluatorNote === 'string') {
          note = cleanString(input.evaluatorNote, 500);
        }

        if (q && (q.type === 'mcq' || q.type === 'true_false')) {
          autoScore += awarded;
        } else {
          manualScore += awarded;
        }

        return {
          question: ans.question,
          answerText: ans.answerText,
          selectedOption: ans.selectedOption,
          awardedMarks: awarded,
          evaluatorNote: note,
        };
      });

      const { totalMarks: effectiveTotalMarks, passingMarks: effectivePassingMarks } = computeEffectiveExamScale(
        exam,
        questions
      );
      const totalScore = Math.min(effectiveTotalMarks, autoScore + manualScore);
      submission.autoScore = autoScore;
      submission.manualScore = manualScore;
      submission.totalScore = totalScore;
      submission.status = 'evaluated';
      submission.evaluatedBy = req.currentUser._id;
      submission.evaluatedAt = new Date();
      await submission.save();

      const publishNow = Boolean(req.body.publish);
      const feedback = cleanString(req.body.feedback || '', 1500);
      const percentage = Math.min(100, Math.round((totalScore / effectiveTotalMarks) * 100));
      const passed = totalScore >= effectivePassingMarks;

      const result = await Result.findOneAndUpdate(
        { submission: submission._id },
        {
          $set: {
            examination: exam._id,
            student: submission.student,
            totalMarks: effectiveTotalMarks,
            obtainedMarks: totalScore,
            percentage,
            grade: formatGrade(percentage),
            passed,
            feedback,
            published: publishNow,
            publishedAt: publishNow ? new Date() : null,
            publishedBy: publishNow ? req.currentUser._id : null,
          },
        },
        { upsert: true, new: true }
      );

      const certOutcome = await upsertCertificateForSubmission({
        submission,
        exam,
        studentUser: submission.student,
        questions,
        resultDoc: result,
      });

      if (publishNow) {
        await Notification.create({
          user: submission.student,
          type: 'result',
          title: `Results Published: ${exam.code}`,
          message: `You scored ${totalScore}/${effectiveTotalMarks} (${percentage}% - Grade ${result.grade}).`,
          linkView: 'results',
        });
      }

      await recordActivity(
        req,
        'SUBMISSION_EVALUATED',
        'Submission',
        submission._id,
        `Evaluated ${exam.code}: ${totalScore}/${effectiveTotalMarks}${publishNow ? ' (Published)' : ''}`
      );

      return res.json({
        success: true,
        message: publishNow ? 'Submission evaluated and result published.' : 'Evaluation saved.',
        submission,
        result,
        certificate: certOutcome ? certOutcome.certificate : null,
      });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- RESULTS ----------------

  app.get('/api/results', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      const filter = isAdmin ? {} : { student: req.currentUser._id, published: true };
      const results = await Result.find(filter)
        .populate('student', 'name email')
        .populate('examination', 'title code course examDate totalMarks passingMarks')
        .sort({ publishedAt: -1, createdAt: -1 })
        .lean();

      await ensureCertificatesBackfilled(isAdmin ? {} : { student: req.currentUser._id });
      const subIds = results.map((r) => r.submission).filter(Boolean);
      const certs = subIds.length ? await Certificate.find({ submission: { $in: subIds } }).lean() : [];
      const certMap = new Map(certs.map((c) => [String(c.submission), c]));
      const enriched = results.map((r) => ({
        ...r,
        certificate: certMap.get(String(r.submission)) || null,
      }));

      return res.json({ success: true, results: enriched });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/results', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const submissionId = req.body.submissionId;
      if (!isValidObjectId(submissionId)) {
        return res.status(400).json({ success: false, message: 'Invalid submission ID.' });
      }
      const submission = await Submission.findById(submissionId);
      if (!submission) {
        return res.status(404).json({ success: false, message: 'Submission not found.' });
      }
      const exam = await Examination.findById(submission.examination).lean();
      if (!exam) {
        return res.status(404).json({ success: false, message: 'Examination not found.' });
      }

      const obtainedMarks =
        req.body.obtainedMarks !== undefined
          ? Math.min(exam.totalMarks, Math.max(0, Number(req.body.obtainedMarks)))
          : submission.totalScore;
      const percentage = Math.min(100, Math.round((obtainedMarks / exam.totalMarks) * 100));
      const passed = obtainedMarks >= exam.passingMarks;
      const published = req.body.published !== false;
      const feedback = cleanString(req.body.feedback || '', 1500);

      const result = await Result.findOneAndUpdate(
        { submission: submission._id },
        {
          $set: {
            examination: exam._id,
            student: submission.student,
            totalMarks: exam.totalMarks,
            obtainedMarks,
            percentage,
            grade: formatGrade(percentage),
            passed,
            feedback,
            published,
            publishedAt: published ? new Date() : null,
            publishedBy: published ? req.currentUser._id : null,
          },
        },
        { upsert: true, new: true }
      );

      await upsertCertificateForSubmission({
        submission,
        exam,
        studentUser: submission.student,
        resultDoc: result,
      });

      if (published) {
        await Notification.create({
          user: submission.student,
          type: 'result',
          title: `Result Available: ${exam.code}`,
          message: `Your result for ${exam.title} has been published (${percentage}%).`,
          linkView: 'results',
        });
      }

      await recordActivity(req, 'RESULT_PUBLISHED', 'Result', result._id, `Published result for ${exam.code}`);
      return res.status(201).json({ success: true, message: 'Result saved and published.', result });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- CERTIFICATES & PUBLIC VERIFICATION ----------------

  app.get('/api/certificates', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      await ensureCertificatesBackfilled(isAdmin ? {} : { student: req.currentUser._id });

      const filter = isAdmin ? {} : { student: req.currentUser._id };
      const batchFilter = cleanString(req.query.batchNumber || '', 60).toUpperCase();
      const search = cleanString(req.query.search || '', 100);
      if (isAdmin && batchFilter) {
        filter.batchNumber = normalizeBatchNumber(batchFilter);
      }
      if (search) {
        const regex = new RegExp(search.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'i');
        filter.$or = [{ certificateNumber: regex }, { studentName: regex }, { courseName: regex }, { examTitle: regex }];
      }

      const certificates = await Certificate.find(filter).sort({ issuedAt: -1, createdAt: -1 }).lean();
      const baseUrl = getSafeResetBaseUrl(req);
      const enriched = certificates.map((c) => ({
        ...c,
        verificationUrl: baseUrl
          ? `${baseUrl}/?verifyCert=${encodeURIComponent(c.certificateNumber)}`
          : `/?verifyCert=${encodeURIComponent(c.certificateNumber)}`,
      }));

      return res.json({ success: true, certificates: enriched });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/certificates/:id/pdf', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid certificate identifier.' });
      }
      const cert = await Certificate.findById(req.params.id).lean();
      if (!cert) {
        return res.status(404).json({ success: false, message: 'Certificate not found.' });
      }

      const isAdmin = req.currentUser.role === 'admin';
      if (!isAdmin && String(cert.student) !== String(req.currentUser._id)) {
        return res.status(403).json({ success: false, message: 'You are not authorized to download this certificate.' });
      }

      const baseUrl = getSafeResetBaseUrl(req);
      const verificationUrl = baseUrl
        ? `${baseUrl}/?verifyCert=${encodeURIComponent(cert.certificateNumber)}`
        : `/?verifyCert=${encodeURIComponent(cert.certificateNumber)}`;

      const pdfBuffer = await buildCertificatePdfBuffer(cert, verificationUrl);
      const safeName = sanitizeFilename(`${cert.certificateNumber}_${cert.studentName}_Certificate.pdf`);
      res.setHeader('Content-Type', 'application/pdf');
      res.setHeader('Content-Disposition', `attachment; filename="${safeName}"`);
      res.setHeader('X-Content-Type-Options', 'nosniff');
      return res.send(pdfBuffer);
    } catch (err) {
      return next(err);
    }
  });

  async function handleCertificateVerification(req, res, next) {
    try {
      const rawCode = req.params.certificateNumber || req.query.certificateNumber || req.query.code || '';
      const certificateNumber = cleanString(String(rawCode), 40)
        .toUpperCase()
        .replace(/[^A-Z0-9-]/g, '');

      if (certificateNumber.length < 4) {
        return res.status(400).json({
          success: false,
          valid: false,
          message: 'Please enter a valid Certificate Number (e.g. CERT-2026-XXXXXXXX).',
        });
      }

      await ensureCertificatesBackfilled({});
      const cert = await Certificate.findOne({ certificateNumber }).lean();
      if (!cert) {
        return res.status(404).json({
          success: false,
          valid: false,
          message: `No certificate record found for "${certificateNumber}".`,
        });
      }

      return res.json({
        success: true,
        valid: cert.status === 'issued',
        certificate: {
          certificateNumber: cert.certificateNumber,
          studentName: cert.studentName,
          studentIdCode: cert.studentIdCode,
          department: cert.department,
          batchNumber: cert.batchNumber,
          courseName: cert.courseName,
          studyOption: cert.studyOption,
          examTitle: cert.examTitle,
          examCode: cert.examCode,
          obtainedMarks: cert.obtainedMarks,
          totalMarks: cert.totalMarks,
          percentage: cert.percentage,
          grade: cert.grade,
          passed: cert.passed,
          status: cert.status,
          issuedAt: cert.issuedAt,
        },
      });
    } catch (err) {
      return next(err);
    }
  }

  app.get('/api/certificates/verify', apiLimiter, handleCertificateVerification);
  app.get('/api/certificates/verify/:certificateNumber', apiLimiter, handleCertificateVerification);

  // ---------------- LECTURES & STUDY MATERIALS ----------------

  app.get('/api/lectures', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      let studentBatch = '';
      const filter = {};

      if (req.query.department) filter.department = cleanString(req.query.department, 100);
      if (req.query.course) filter.course = cleanString(req.query.course, 120);

      if (!isAdmin) {
        const profile = await StudentProfile.findOne({ user: req.currentUser._id }).select('batchNumber').lean();
        studentBatch = normalizeBatchNumber((profile && profile.batchNumber) || 'BATCH-01') || 'BATCH-01';
        filter.batchNumber = studentBatch;
        filter.status = 'published';
      } else {
        if (req.query.batchNumber) filter.batchNumber = normalizeBatchNumber(req.query.batchNumber);
        if (req.query.status && ['published', 'draft'].includes(req.query.status)) filter.status = req.query.status;
      }

      const [lectures, allDepts, allBatches] = await Promise.all([
        Lecture.find(filter).sort({ batchNumber: 1, course: 1, order: 1, createdAt: -1 }).lean(),
        Department.find({}).select('name code courses').lean(),
        Batch.find({ status: 'active' }).select('batchNumber department course studyOption').lean(),
      ]);

      const departments = allDepts.map((d) => d.name);
      const courses = Array.from(
        new Set([...allDepts.flatMap((d) => (d.courses || []).map((c) => c.title)), ...lectures.map((l) => l.course)])
      ).filter(Boolean).sort();
      const batches = Array.from(
        new Set([...allBatches.map((b) => (b.batchNumber || '').toUpperCase()), ...lectures.map((l) => l.batchNumber)])
      ).filter(Boolean).sort();

      return res.json({
        success: true,
        lectures,
        studentBatch: !isAdmin ? studentBatch : undefined,
        metadata: { departments, courses, batches },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/lectures', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const title = cleanString(req.body.title, 160);
      const code = cleanString(req.body.code, 40).toUpperCase();
      const department = cleanString(req.body.department || 'Computer Science', 100);
      const course = cleanString(req.body.course, 120);
      const batchNumber = await resolveAllocatedBatch(req.body.batchNumber, 'BATCH-01');
      const studyOption = cleanString(req.body.studyOption || '', 80);
      const type = ['video_upload', 'video_link', 'pdf_document', 'reading'].includes(req.body.type)
        ? req.body.type
        : 'video_upload';
      const videoUrl = cleanString(req.body.videoUrl || '', 1000);
      const fileMetaId = isValidObjectId(req.body.fileMetaId) ? req.body.fileMetaId : null;
      const filename = cleanString(req.body.filename || '', 160);
      const mimeType = cleanString(req.body.mimeType || '', 120);
      const fileSize = Number(req.body.fileSize) || 0;
      const description = cleanString(req.body.description, 2000);
      const durationMinutes = Math.min(600, Math.max(1, Number.parseInt(req.body.durationMinutes, 10) || 30));
      const order = Number.parseInt(req.body.order, 10) || ((await Lecture.countDocuments({ batchNumber, course })) + 1);
      const status = ['published', 'draft'].includes(req.body.status) ? req.body.status : 'published';

      if (title.length < 3 || !course) {
        return res.status(400).json({ success: false, message: 'Lecture title (min 3 chars) and course are required.' });
      }

      const lecture = await Lecture.create({
        title,
        code,
        department,
        course,
        batchNumber,
        studyOption,
        type,
        videoUrl,
        fileMetaId,
        filename,
        mimeType,
        fileSize,
        description,
        durationMinutes,
        order,
        status,
        createdBy: req.currentUser._id,
      });

      await Batch.updateOne(
        { batchNumber },
        {
          $setOnInsert: {
            batchNumber,
            department,
            course,
            studyOption,
            status: 'active',
            createdBy: req.currentUser._id,
          },
        },
        { upsert: true }
      );

      // Notify enrolled students in this batch
      const targetStudents = await StudentProfile.find({ batchNumber }).select('user').lean();
      const studentUserIds = targetStudents.map((p) => p.user);
      if (studentUserIds.length && status === 'published') {
        await Notification.insertMany(
          studentUserIds.map((uid) => ({
            user: uid,
            type: 'announcement',
            title: `New Lecture: ${course}`,
            message: `${title} has been published for your batch (${batchNumber}).`,
            linkView: 'lectures',
          }))
        );
      }

      await recordActivity(
        req,
        'LECTURE_CREATED',
        'Lecture',
        lecture._id,
        `Created lecture "${title}" for course ${course} (${batchNumber})`
      );
      return res.status(201).json({ success: true, message: `Lecture "${title}" published successfully.`, lecture });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/lectures/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid lecture identifier.' });
      }
      const lecture = await Lecture.findById(req.params.id);
      if (!lecture) {
        return res.status(404).json({ success: false, message: 'Lecture not found.' });
      }

      if (req.body.title) lecture.title = cleanString(req.body.title, 160);
      if (req.body.code !== undefined) lecture.code = cleanString(req.body.code, 40).toUpperCase();
      if (req.body.department) lecture.department = cleanString(req.body.department, 100);
      if (req.body.course) lecture.course = cleanString(req.body.course, 120);
      if (req.body.batchNumber) lecture.batchNumber = normalizeBatchNumber(req.body.batchNumber);
      if (req.body.studyOption !== undefined) lecture.studyOption = cleanString(req.body.studyOption, 80);
      if (['video_upload', 'video_link', 'pdf_document', 'reading'].includes(req.body.type)) lecture.type = req.body.type;
      if (req.body.videoUrl !== undefined) lecture.videoUrl = cleanString(req.body.videoUrl, 1000);
      if (isValidObjectId(req.body.fileMetaId)) lecture.fileMetaId = req.body.fileMetaId;
      if (req.body.filename !== undefined) lecture.filename = cleanString(req.body.filename, 160);
      if (req.body.mimeType !== undefined) lecture.mimeType = cleanString(req.body.mimeType, 120);
      if (req.body.description !== undefined) lecture.description = cleanString(req.body.description, 2000);
      if (req.body.durationMinutes) lecture.durationMinutes = Math.min(600, Math.max(1, Number(req.body.durationMinutes)));
      if (['published', 'draft'].includes(req.body.status)) lecture.status = req.body.status;

      await lecture.save();
      await recordActivity(req, 'LECTURE_UPDATED', 'Lecture', lecture._id, `Updated lecture "${lecture.title}"`);
      return res.json({ success: true, message: 'Lecture updated successfully.', lecture });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/lectures/:id', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid lecture identifier.' });
      }
      const lecture = await Lecture.findById(req.params.id);
      if (!lecture) {
        return res.status(404).json({ success: false, message: 'Lecture not found.' });
      }
      await Lecture.deleteOne({ _id: lecture._id });
      await recordActivity(req, 'LECTURE_DELETED', 'Lecture', lecture._id, `Removed lecture "${lecture.title}"`);
      return res.json({ success: true, message: `Lecture "${lecture.title}" removed.` });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/wallet', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      if (isAdmin && !req.query.userId) {
        const wallets = await Wallet.find()
          .populate('user', 'name email role status')
          .sort({ balance: -1 })
          .lean();
        const profiles = await StudentProfile.find().select('user studentId department').lean();
        const pMap = new Map(profiles.map((p) => [String(p.user), p]));
        const enriched = wallets.map((w) => ({
          ...w,
          studentId: w.user ? (pMap.get(String(w.user._id)) || {}).studentId || '' : '',
          department: w.user ? (pMap.get(String(w.user._id)) || {}).department || '' : '',
        }));
        const totalBalance = enriched.reduce((sum, w) => sum + (w.balance || 0), 0);
        return res.json({ success: true, wallets: enriched, totalBalance });
      }

      const targetUserId = isAdmin && isValidObjectId(req.query.userId) ? req.query.userId : req.currentUser._id;
      let wallet = await Wallet.findOne({ user: targetUserId }).lean();
      if (!wallet && !isAdmin) {
        wallet = await Wallet.create({ user: targetUserId, balance: 0, currency: 'USD' });
      }
      return res.json({ success: true, wallet });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/wallet/transactions', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      const filter = isAdmin ? {} : { user: req.currentUser._id };
      if (isAdmin && req.query.userId && isValidObjectId(req.query.userId)) {
        filter.user = req.query.userId;
      }
      if (req.query.type && ['credit', 'debit'].includes(req.query.type)) {
        filter.type = req.query.type;
      }

      const transactions = await WalletTransaction.find(filter)
        .populate('user', 'name email')
        .populate('createdBy', 'name role')
        .sort({ createdAt: -1 })
        .limit(100)
        .lean();

      return res.json({ success: true, transactions });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/wallet/adjust', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const userId = req.body.userId;
      const type = req.body.type;
      const amount = Number(req.body.amount);
      const description = cleanString(req.body.description, 300);
      const category = ['scholarship', 'exam_fee', 'refund', 'adjustment', 'reward'].includes(req.body.category)
        ? req.body.category
        : 'adjustment';

      if (!isValidObjectId(userId)) {
        return res.status(400).json({ success: false, message: 'Valid student user ID is required.' });
      }
      if (!['credit', 'debit'].includes(type)) {
        return res.status(400).json({ success: false, message: 'Transaction type must be credit or debit.' });
      }
      if (!Number.isFinite(amount) || amount <= 0 || amount > 100000) {
        return res.status(400).json({ success: false, message: 'Amount must be between $0.01 and $100,000.' });
      }
      if (!description) {
        return res.status(400).json({ success: false, message: 'Transaction description is required.' });
      }

      const student = await User.findOne({ _id: userId, role: 'student' }).lean();
      if (!student) {
        return res.status(404).json({ success: false, message: 'Target student account not found.' });
      }

      // Atomic conditional balance update
      const filter = { user: userId, status: 'active' };
      if (type === 'debit') {
        filter.balance = { $gte: amount };
      }

      const delta = type === 'credit' ? amount : -amount;
      const updatedWallet = await Wallet.findOneAndUpdate(
        filter,
        { $inc: { balance: delta } },
        { new: true }
      );

      if (!updatedWallet) {
        return res.status(400).json({
          success: false,
          message: type === 'debit' ? 'Insufficient wallet balance for this debit.' : 'Wallet is frozen or unavailable.',
        });
      }

      const balanceAfter = Number(updatedWallet.balance.toFixed(2));
      const balanceBefore = Number((balanceAfter - delta).toFixed(2));
      const reference = `TXN-${Date.now()}-${crypto.randomBytes(3).toString('hex').toUpperCase()}`;

      const tx = await WalletTransaction.create({
        wallet: updatedWallet._id,
        user: userId,
        type,
        amount,
        balanceBefore,
        balanceAfter,
        reference,
        description,
        category,
        status: 'completed',
        createdBy: req.currentUser._id,
      });

      await Notification.create({
        user: userId,
        type: 'account',
        title: `Wallet ${type === 'credit' ? 'Credited' : 'Debited'}: $${amount.toFixed(2)}`,
        message: `${description} (Ref: ${reference})`,
        linkView: 'wallet',
      });

      await recordActivity(
        req,
        'WALLET_ADJUSTED',
        'WalletTransaction',
        tx._id,
        `${type.toUpperCase()} $${amount.toFixed(2)} for ${student.email} (${reference})`
      );

      return res.status(201).json({
        success: true,
        message: `Wallet ${type} of $${amount.toFixed(2)} processed.`,
        wallet: updatedWallet,
        transaction: tx,
      });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- MESSAGES & INBOX ----------------

  app.get('/api/messages/recipients', requireAuth, async (req, res, next) => {
    try {
      const isAdmin = req.currentUser.role === 'admin';
      const query = isAdmin
        ? { _id: { $ne: req.currentUser._id }, status: 'active' }
        : { role: 'admin', status: 'active' };
      const users = await User.find(query).select('name email role').sort({ role: 1, name: 1 }).lean();
      return res.json({ success: true, recipients: users });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/messages', requireAuth, async (req, res, next) => {
    try {
      const folder = req.query.folder === 'sent' ? 'sent' : 'inbox';
      const search = cleanString(req.query.q || '', 100);

      const filter =
        folder === 'sent'
          ? { sender: req.currentUser._id, deletedBySender: false }
          : { recipient: req.currentUser._id, deletedByRecipient: false };

      if (search) {
        const regex = new RegExp(search.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'i');
        filter.$or = [{ subject: regex }, { body: regex }];
      }

      const [messages, unreadCount] = await Promise.all([
        Message.find(filter)
          .populate('sender', 'name email role')
          .populate('recipient', 'name email role')
          .sort({ createdAt: -1 })
          .limit(100)
          .lean(),
        Message.countDocuments({ recipient: req.currentUser._id, isRead: false, deletedByRecipient: false }),
      ]);

      return res.json({ success: true, folder, messages, unreadCount });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/messages', requireAuth, async (req, res, next) => {
    try {
      const recipientId = req.body.recipientId;
      const subject = cleanString(req.body.subject, 180);
      const body = cleanString(req.body.body, 4000);

      if (!isValidObjectId(recipientId)) {
        return res.status(400).json({ success: false, message: 'Valid recipient is required.' });
      }
      if (!subject || !body) {
        return res.status(400).json({ success: false, message: 'Subject and message body are required.' });
      }

      const recipient = await User.findOne({ _id: recipientId, status: 'active' }).lean();
      if (!recipient) {
        return res.status(404).json({ success: false, message: 'Recipient not found.' });
      }
      if (req.currentUser.role === 'student' && recipient.role !== 'admin') {
        return res.status(403).json({ success: false, message: 'Students can message administrators only.' });
      }

      const message = await Message.create({
        sender: req.currentUser._id,
        recipient: recipient._id,
        subject,
        body,
      });

      await Notification.create({
        user: recipient._id,
        type: 'message',
        title: `New Message from ${req.currentUser.name}`,
        message: subject,
        linkView: 'messages',
      });

      return res.status(201).json({ success: true, message: 'Message sent.', data: message });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/messages/:id/read', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid message ID.' });
      }
      const msg = await Message.findOneAndUpdate(
        { _id: req.params.id, recipient: req.currentUser._id },
        { $set: { isRead: true, readAt: new Date() } },
        { new: true }
      );
      if (!msg) {
        return res.status(404).json({ success: false, message: 'Message not found.' });
      }
      return res.json({ success: true, message: 'Marked as read.' });
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/messages/:id', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid message ID.' });
      }
      const msg = await Message.findById(req.params.id);
      if (!msg) {
        return res.status(404).json({ success: false, message: 'Message not found.' });
      }

      const uid = String(req.currentUser._id);
      if (String(msg.sender) !== uid && String(msg.recipient) !== uid) {
        return res.status(403).json({ success: false, message: 'Not authorized to delete this message.' });
      }

      if (String(msg.sender) === uid) msg.deletedBySender = true;
      if (String(msg.recipient) === uid) msg.deletedByRecipient = true;

      if (msg.deletedBySender && msg.deletedByRecipient) {
        await Message.deleteOne({ _id: msg._id });
      } else {
        await msg.save();
      }
      return res.json({ success: true, message: 'Message removed.' });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- NOTIFICATIONS ----------------

  app.get('/api/notifications', requireAuth, async (req, res, next) => {
    try {
      const [notifications, unreadCount] = await Promise.all([
        Notification.find({ user: req.currentUser._id }).sort({ createdAt: -1 }).limit(50).lean(),
        Notification.countDocuments({ user: req.currentUser._id, isRead: false }),
      ]);
      return res.json({ success: true, notifications, unreadCount });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/notifications/read-all', requireAuth, async (req, res, next) => {
    try {
      await Notification.updateMany(
        { user: req.currentUser._id, isRead: false },
        { $set: { isRead: true, readAt: new Date() } }
      );
      return res.json({ success: true, message: 'All notifications marked as read.' });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/notifications/:id/read', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid notification ID.' });
      }
      const notif = await Notification.findOneAndUpdate(
        { _id: req.params.id, user: req.currentUser._id },
        { $set: { isRead: true, readAt: new Date() } },
        { new: true }
      );
      if (!notif) {
        return res.status(404).json({ success: false, message: 'Notification not found.' });
      }
      return res.json({ success: true, notification: notif });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/notifications/broadcast', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const title = cleanString(req.body.title, 160);
      const message = cleanString(req.body.message, 600);
      if (!title || !message) {
        return res.status(400).json({ success: false, message: 'Title and message are required.' });
      }
      const students = await User.find({ role: 'student', status: 'active' }).select('_id').lean();
      if (students.length) {
        await Notification.insertMany(
          students.map((s) => ({
            user: s._id,
            type: 'announcement',
            title,
            message,
            linkView: 'notifications',
          }))
        );
      }
      await recordActivity(req, 'ANNOUNCEMENT_BROADCAST', 'Notification', '', `Broadcast: ${title}`);
      return res.status(201).json({ success: true, message: `Announcement sent to ${students.length} students.` });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- PROFILE & PHOTO UPLOAD ----------------

  app.get('/api/profile', requireAuth, async (req, res, next) => {
    try {
      const profile =
        req.currentUser.role === 'student'
          ? await StudentProfile.findOne({ user: req.currentUser._id }).lean()
          : null;
      return res.json({
        success: true,
        user: {
          id: req.currentUser._id,
          name: req.currentUser.name,
          email: req.currentUser.email,
          role: req.currentUser.role,
          status: req.currentUser.status,
          createdAt: req.currentUser.createdAt,
          avatarBase64: (profile && profile.avatarBase64) || req.currentUser.avatarBase64 || '',
        },
        profile,
      });
    } catch (err) {
      return next(err);
    }
  });

  app.put('/api/profile', requireAuth, async (req, res, next) => {
    try {
      const name = cleanString(req.body.name || req.currentUser.name, 100);
      if (name.length < 2) {
        return res.status(400).json({ success: false, message: 'Name must be at least 2 characters.' });
      }
      await User.updateOne({ _id: req.currentUser._id }, { $set: { name } });

      if (req.currentUser.role === 'student') {
        const updates = {
          phone: cleanString(req.body.phone, 30),
          address: cleanString(req.body.address, 250),
          department: cleanString(req.body.department, 100),
          program: cleanString(req.body.program, 100),
          semester: cleanString(req.body.semester, 40),
          guardianName: cleanString(req.body.guardianName, 100),
          guardianPhone: cleanString(req.body.guardianPhone, 30),
          bio: cleanString(req.body.bio, 500),
        };
        if (['Male', 'Female', 'Non-Binary', 'Prefer not to say', ''].includes(req.body.gender)) {
          updates.gender = req.body.gender;
        }
        if (req.body.dateOfBirth && !Number.isNaN(new Date(req.body.dateOfBirth).getTime())) {
          updates.dateOfBirth = new Date(req.body.dateOfBirth);
        }
        await StudentProfile.updateOne({ user: req.currentUser._id }, { $set: updates });
      }

      await recordActivity(req, 'PROFILE_UPDATED', 'User', req.currentUser._id, 'Updated profile details');
      return res.json({ success: true, message: 'Profile updated successfully.' });
    } catch (err) {
      return next(err);
    }
  });

  app.post('/api/profile/photo', requireAuth, async (req, res, next) => {
    try {
      const parsed = parseAndValidateBase64Upload(
        req.body.data,
        req.body.filename || 'avatar.png',
        req.body.mimeType,
        'image'
      );

      await User.updateOne({ _id: req.currentUser._id }, { $set: { avatarBase64: parsed.dataUri } });
      if (req.currentUser.role === 'student') {
        await StudentProfile.updateOne({ user: req.currentUser._id }, { $set: { avatarBase64: parsed.dataUri } });
      }

      await recordActivity(req, 'PROFILE_PHOTO_UPDATED', 'User', req.currentUser._id, 'Uploaded profile photo');
      return res.json({
        success: true,
        message: 'Profile photo updated.',
        avatarBase64: parsed.dataUri,
      });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- FILES (BASE64 + MONGODB GRIDFS) ----------------

  app.post('/api/files/upload', requireAuth, async (req, res, next) => {
    try {
      if (!gridFsBucket) {
        return res.status(503).json({ success: false, message: 'File storage service unavailable.' });
      }

      const category = ['question_file', 'answer_file', 'exam_resource', 'lecture_file'].includes(req.body.category)
        ? req.body.category
        : 'answer_file';

      if (category !== 'answer_file' && req.currentUser.role !== 'admin') {
        return res.status(403).json({ success: false, message: 'Only administrators can upload restricted resources.' });
      }

      const parsed = parseAndValidateBase64Upload(
        req.body.data,
        req.body.filename || 'document',
        req.body.mimeType,
        category === 'lecture_file' ? 'document' : 'document'
      );

      const uploadStream = gridFsBucket.openUploadStream(parsed.safeFilename, {
        contentType: parsed.mimeType,
        metadata: {
          uploadedBy: String(req.currentUser._id),
          category,
        },
      });

      await new Promise((resolve, reject) => {
        uploadStream.on('error', reject);
        uploadStream.on('finish', resolve);
        uploadStream.end(parsed.buffer);
      });

      const meta = await FileMeta.create({
        gridFsId: uploadStream.id,
        uploadedBy: req.currentUser._id,
        category,
        filename: parsed.safeFilename,
        mimeType: parsed.mimeType,
        size: parsed.size,
        relatedExam: isValidObjectId(req.body.relatedExam) ? req.body.relatedExam : null,
        relatedLecture: isValidObjectId(req.body.relatedLecture) ? req.body.relatedLecture : null,
      });

      await recordActivity(req, 'FILE_UPLOADED', 'FileMeta', meta._id, `Uploaded ${parsed.safeFilename} (${category})`);
      return res.status(201).json({
        success: true,
        message: 'File uploaded securely.',
        file: {
          id: meta.gridFsId,
          filename: meta.filename,
          mimeType: meta.mimeType,
          size: meta.size,
          category: meta.category,
        },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/files/:id', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid file ID.' });
      }
      const fileId = new mongoose.Types.ObjectId(req.params.id);
      const meta = await FileMeta.findOne({ gridFsId: fileId }).lean();
      if (!meta) {
        return res.status(404).json({ success: false, message: 'File not found.' });
      }

      const isAdmin = req.currentUser.role === 'admin';
      const isOwner = String(meta.uploadedBy) === String(req.currentUser._id);
      const isExamOrLectureResource =
        meta.category === 'question_file' ||
        meta.category === 'exam_resource' ||
        meta.category === 'lecture_file';

      if (!isAdmin && !isOwner && !isExamOrLectureResource) {
        return res.status(403).json({ success: false, message: 'Not authorized to download this file.' });
      }

      res.setHeader('Content-Type', meta.mimeType);
      res.setHeader('Content-Disposition', `attachment; filename="${sanitizeFilename(meta.filename)}"`);
      res.setHeader('X-Content-Type-Options', 'nosniff');

      const downloadStream = gridFsBucket.openDownloadStream(fileId);
      downloadStream.on('error', () => {
        if (!res.headersSent) {
          res.status(404).json({ success: false, message: 'File content missing.' });
        }
      });
      return downloadStream.pipe(res);
    } catch (err) {
      return next(err);
    }
  });

  app.delete('/api/files/:id', requireAuth, async (req, res, next) => {
    try {
      if (!isValidObjectId(req.params.id)) {
        return res.status(400).json({ success: false, message: 'Invalid file ID.' });
      }
      const fileId = new mongoose.Types.ObjectId(req.params.id);
      const meta = await FileMeta.findOne({ gridFsId: fileId });
      if (!meta) {
        return res.status(404).json({ success: false, message: 'File not found.' });
      }
      if (req.currentUser.role !== 'admin' && String(meta.uploadedBy) !== String(req.currentUser._id)) {
        return res.status(403).json({ success: false, message: 'Not authorized to delete this file.' });
      }
      await gridFsBucket.delete(fileId).catch(() => {});
      await FileMeta.deleteOne({ _id: meta._id });
      return res.json({ success: true, message: 'File deleted.' });
    } catch (err) {
      return next(err);
    }
  });

  // ---------------- REPORTS & ANALYTICS (ADMIN) ----------------

  app.get('/api/reports/dashboard', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const [deptStats, examStats, resultSummary, walletMonthly] = await Promise.all([
        StudentProfile.aggregate([
          { $group: { _id: '$department', count: { $sum: 1 } } },
          { $sort: { count: -1 } },
        ]),
        Examination.aggregate([
          { $group: { _id: '$status', count: { $sum: 1 } } },
        ]),
        Result.aggregate([
          {
            $group: {
              _id: '$grade',
              count: { $sum: 1 },
              avgPct: { $avg: '$percentage' },
            },
          },
          { $sort: { _id: 1 } },
        ]),
        WalletTransaction.aggregate([
          {
            $group: {
              _id: '$category',
              totalAmount: { $sum: '$amount' },
              count: { $sum: 1 },
            },
          },
        ]),
      ]);

      return res.json({
        success: true,
        analytics: {
          departments: deptStats.map((d) => ({ label: d._id || 'Unassigned', count: d.count })),
          examStatus: examStats.map((e) => ({ label: e._id, count: e.count })),
          gradeDistribution: resultSummary.map((g) => ({
            grade: g._id,
            count: g.count,
            avgPct: Math.round(g.avgPct || 0),
          })),
          walletCategories: walletMonthly.map((w) => ({
            category: w._id,
            totalAmount: Number(w.totalAmount.toFixed(2)),
            count: w.count,
          })),
        },
      });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/reports/students', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const dateFilter = {};
      if (req.query.from && !Number.isNaN(new Date(req.query.from).getTime())) {
        dateFilter.$gte = new Date(req.query.from);
      }
      if (req.query.to && !Number.isNaN(new Date(req.query.to).getTime())) {
        const toDate = new Date(req.query.to);
        toDate.setHours(23, 59, 59, 999);
        dateFilter.$lte = toDate;
      }

      const userQuery = { role: 'student' };
      if (Object.keys(dateFilter).length) userQuery.createdAt = dateFilter;

      const users = await User.find(userQuery).sort({ createdAt: -1 }).lean();
      const userIds = users.map((u) => u._id);
      const [profiles, wallets] = await Promise.all([
        StudentProfile.find({ user: { $in: userIds } }).lean(),
        Wallet.find({ user: { $in: userIds } }).lean(),
      ]);

      const pMap = new Map(profiles.map((p) => [String(p.user), p]));
      const wMap = new Map(wallets.map((w) => [String(w.user), w]));

      const rows = users.map((u) => {
        const p = pMap.get(String(u._id)) || {};
        const w = wMap.get(String(u._id)) || { balance: 0 };
        return {
          studentId: p.studentId || '',
          name: u.name,
          email: u.email,
          department: p.department || '',
          batchNumber: p.batchNumber || 'BATCH-01',
          program: p.program || '',
          semester: p.semester || '',
          status: u.status,
          walletBalance: w.balance || 0,
          registeredAt: u.createdAt,
        };
      });

      if (req.query.format === 'csv') {
        const headers = ['Student ID', 'Name', 'Email', 'Department', 'Batch Number', 'Program', 'Semester', 'Status', 'Wallet Balance', 'Registered At'];
        const csvLines = [
          headers.join(','),
          ...rows.map((r) =>
            [
              r.studentId,
              r.name,
              r.email,
              r.department,
              r.batchNumber,
              r.program,
              r.semester,
              r.status,
              r.walletBalance,
              new Date(r.registeredAt).toISOString(),
            ]
              .map(escapeCsvCell)
              .join(',')
          ),
        ];
        res.setHeader('Content-Type', 'text/csv; charset=utf-8');
        res.setHeader('Content-Disposition', 'attachment; filename="students_report.csv"');
        return res.send(csvLines.join('\n'));
      }

      return res.json({ success: true, rows });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/reports/examinations', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const exams = await Examination.find().sort({ examDate: -1 }).lean();
      const [subs, results] = await Promise.all([
        Submission.aggregate([
          { $group: { _id: '$examination', count: { $sum: 1 }, avgScore: { $avg: '$totalScore' } } },
        ]),
        Result.aggregate([
          {
            $group: {
              _id: '$examination',
              publishedCount: { $sum: 1 },
              passCount: { $sum: { $cond: ['$passed', 1, 0] } },
            },
          },
        ]),
      ]);

      const sMap = new Map(subs.map((s) => [String(s._id), s]));
      const rMap = new Map(results.map((r) => [String(r._id), r]));

      const rows = exams.map((e) => {
        const s = sMap.get(String(e._id)) || { count: 0, avgScore: 0 };
        const r = rMap.get(String(e._id)) || { publishedCount: 0, passCount: 0 };
        return {
          code: e.code,
          title: e.title,
          course: e.course,
          examDate: e.examDate,
          status: e.status,
          totalMarks: e.totalMarks,
          submissions: s.count,
          avgScore: Math.round((s.avgScore || 0) * 10) / 10,
          publishedResults: r.publishedCount,
          passRate: r.publishedCount ? Math.round((r.passCount / r.publishedCount) * 100) : 0,
        };
      });

      if (req.query.format === 'csv') {
        const headers = ['Code', 'Title', 'Course', 'Date', 'Status', 'Total Marks', 'Submissions', 'Avg Score', 'Published Results', 'Pass Rate %'];
        const csvLines = [
          headers.join(','),
          ...rows.map((r) =>
            [
              r.code,
              r.title,
              r.course,
              new Date(r.examDate).toISOString(),
              r.status,
              r.totalMarks,
              r.submissions,
              r.avgScore,
              r.publishedResults,
              r.passRate,
            ]
              .map(escapeCsvCell)
              .join(',')
          ),
        ];
        res.setHeader('Content-Type', 'text/csv; charset=utf-8');
        res.setHeader('Content-Disposition', 'attachment; filename="examinations_report.csv"');
        return res.send(csvLines.join('\n'));
      }

      return res.json({ success: true, rows });
    } catch (err) {
      return next(err);
    }
  });

  app.get('/api/reports/wallet', requireAuth, requireRole('admin'), async (req, res, next) => {
    try {
      const transactions = await WalletTransaction.find()
        .populate('user', 'name email')
        .sort({ createdAt: -1 })
        .limit(500)
        .lean();

      if (req.query.format === 'csv') {
        const headers = ['Reference', 'Student', 'Email', 'Type', 'Category', 'Amount', 'Balance Before', 'Balance After', 'Description', 'Date'];
        const csvLines = [
          headers.join(','),
          ...transactions.map((t) =>
            [
              t.reference,
              t.user ? t.user.name : '',
              t.user ? t.user.email : '',
              t.type,
              t.category,
              t.amount,
              t.balanceBefore,
              t.balanceAfter,
              t.description,
              new Date(t.createdAt).toISOString(),
            ]
              .map(escapeCsvCell)
              .join(',')
          ),
        ];
        res.setHeader('Content-Type', 'text/csv; charset=utf-8');
        res.setHeader('Content-Disposition', 'attachment; filename="wallet_transactions_report.csv"');
        return res.send(csvLines.join('\n'));
      }

      return res.json({ success: true, rows: transactions });
    } catch (err) {
      return next(err);
    }
  });
}

// ============================================================================
// 9. 404 & CENTRALIZED ERROR HANDLERS
// ============================================================================

function registerErrorHandlers() {
  app.use('/api', (_req, res) => {
    res.status(404).json({ success: false, message: 'API endpoint not found.' });
  });

  app.use((_req, res) => {
    res.status(404).redirect('/');
  });

  app.use((err, _req, res, _next) => {
    if (err && err.type === 'entity.too.large') {
      return res.status(413).json({ success: false, message: 'Payload exceeds the maximum 8 MB limit.' });
    }
    if (err && err.code === 11000) {
      return res.status(409).json({ success: false, message: 'Duplicate record conflict.' });
    }
    if (err && err.name === 'ValidationError') {
      const firstErr = Object.values(err.errors || {})[0];
      return res.status(400).json({
        success: false,
        message: firstErr ? firstErr.message : 'Validation failed.',
      });
    }

    const status = err.status || 500;
    console.error('[Server Error]', err);
    return res.status(status).json({
      success: false,
      message: status >= 500 ? 'An unexpected server error occurred. Please try again.' : err.message,
    });
  });
}

// ============================================================================
// 10. BOOTSTRAP & GRACEFUL SHUTDOWN
// ============================================================================

let appReady = false;
let appReadyPromise = null;
let gateRegistered = false;
let routesConfigured = false;
let lastInitError = '';

function escapeBasicHtml(str) {
  return String(str || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

function registerHealthAndReadinessGate() {
  if (gateRegistered) return;
  gateRegistered = true;

  app.get('/health', (_req, res) => {
    const dbReady = mongoose.connection.readyState === 1;
    res.status(200).json({
      success: dbReady && appReady,
      status: dbReady && appReady ? 'healthy' : lastInitError ? 'error' : 'initializing',
      dbReady,
      dbMode,
      databaseName: mongoose.connection.name || '',
      hasMongoUriEnv: Boolean(process.env.MONGODB_URI && process.env.MONGODB_URI.trim()),
      fallbackReason: dbFallbackReason || lastInitError || undefined,
      timestamp: new Date().toISOString(),
    });
  });

  app.use(async (req, res, next) => {
    if (appReady) return next();
    try {
      await ensureInitialized();
      return next();
    } catch (err) {
      const msg = dbFallbackReason || (err && err.message) || 'Portal database initialization failed.';
      if (req.path.startsWith('/api')) {
        return res.status(503).json({
          success: false,
          message: msg,
        });
      }
      return res
        .status(503)
        .type('html')
        .send(
          `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>EduPulse Portal — Setup Required</title><style>body{font-family:system-ui,-apple-system,sans-serif;background:#F2F5F7;color:#333;display:flex;align-items:center;justify-content:center;min-height:100vh;margin:0;padding:24px}.card{max-width:560px;background:#fff;border-radius:12px;padding:28px;box-shadow:0 4px 15px rgba(0,0,0,.1);border-top:5px solid #0F5298}h1{margin:0 0 10px;font-size:20px;color:#0F5298}p{margin:8px 0;line-height:1.55;font-size:14px}.err{background:#FDECEA;color:#B42318;padding:12px 14px;border-radius:8px;font-size:13px;margin:14px 0;word-break:break-word}code{background:#EEF2F6;padding:2px 6px;border-radius:4px}</style></head><body><div class="card"><h1>EduPulse Portal — Database Connection Required</h1><p>The server started, but could not complete database initialization:</p><div class="err">${escapeBasicHtml(msg)}</div><p>On Vercel, open <strong>Project Settings → Environment Variables</strong>, add <code>MONGODB_URI</code> (and <code>SESSION_SECRET</code>), ensure MongoDB Atlas Network Access allows <code>0.0.0.0/0</code>, and redeploy.</p></div></body></html>`
        );
    }
  });
}

function ensureInitialized() {
  registerHealthAndReadinessGate();
  if (!appReadyPromise) {
    appReadyPromise = (async () => {
      lastInitError = '';
      await connectDatabase();
      if (!routesConfigured) {
        configureSessionMiddleware();
        registerRoutes();
        registerErrorHandlers();
        routesConfigured = true;
      }
      await seedInitialData();
      appReady = true;
      console.log(`[Server] EduPulse Portal ready (dbMode=${dbMode}, env=${NODE_ENV})`);
    })().catch((err) => {
      lastInitError = (err && err.message) || 'Initialization failed.';
      appReadyPromise = null;
      throw err;
    });
  }
  return appReadyPromise;
}

async function startServer() {
  try {
    registerHealthAndReadinessGate();

    httpServer = app.listen(PORT, '0.0.0.0', () => {
      console.log(`[Server] EduPulse Portal listening on http://0.0.0.0:${PORT} (${NODE_ENV})`);
    });

    await ensureInitialized();
  } catch (err) {
    console.error('[Fatal] Failed to start server:', err);
    process.exit(1);
  }
}

async function shutdown(signal) {
  console.log(`[Shutdown] Received ${signal}. Closing server gracefully...`);
  try {
    if (httpServer) {
      await new Promise((resolve) => httpServer.close(resolve));
    }
    await mongoose.connection.close();
    if (memoryServerInstance) {
      await memoryServerInstance.stop();
    }
    console.log('[Shutdown] Clean exit complete.');
    process.exit(0);
  } catch (err) {
    console.error('[Shutdown] Error during shutdown:', err);
    process.exit(1);
  }
}

if (require.main === module) {
  process.on('SIGINT', () => shutdown('SIGINT'));
  process.on('SIGTERM', () => shutdown('SIGTERM'));
  startServer();
}

module.exports = async (req, res) => {
  registerHealthAndReadinessGate();
  if (req.url !== '/health') {
    try {
      await ensureInitialized();
    } catch (_err) {
      // Readiness gate middleware renders diagnostic 503 response
    }
  }
  return app(req, res);
};
