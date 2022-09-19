package com.github.tgeng.archon.common

opaque type Timestamp = Long

extension(t1: Timestamp) {
  def <(t2: Timestamp) = t1 < t2
  def >(t2: Timestamp) = t1 > t2
  def <=(t2: Timestamp) = t1 <= t2
  def >=(t2: Timestamp) = t1 >= t2
}

import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.ObjectInputStream
import java.io.ObjectOutputStream
import java.nio.charset.StandardCharsets.*
import java.nio.file.{Files, Paths}
import java.io.IOException
import scala.collection.immutable.ArraySeq

extension(f: File) {

  def timestamp: Timestamp = f.lastModified

  def readText(): String = String(Files.readAllBytes(f.toPath), UTF_8)

  def writeText(s: String) = {
    f.getParentFile.!!.mkDirsPlease
    Files.write(f.toPath, s.getBytes(UTF_8))
  }

  def readObject[T]: T = {
    val ois = ObjectInputStream(FileInputStream(f))
    try {
      return ois.readObject.asInstanceOf[T]
    } finally {
      ois.close
    }
  }

  def writeObject[T](t: T): Unit = {
    f.getParentFile.!!.mkDirsPlease
    val oos = ObjectOutputStream(FileOutputStream(f))
    try {
      oos.writeObject(t)
    } finally {
      oos.close
    }
  }

  def mkDirsPlease = Files.createDirectories(f.toPath)

  def /(s: String) = File(f, s)

  def deleteRecursively: Unit = {
    if (f.isDirectory) {
      f.listFiles.!!.foreach(f => f.!!.deleteRecursively)
    }
    if (f.exists && !f.delete) {
      throw IOException(s"Unable to delete ${f.getAbsolutePath}")
    }
  }

  def children: Map[String, File] = {
    val childrenNames = f.list
    if (childrenNames == null) Map.empty
    else childrenNames.map(name => (name.!!, f / name.!!)).toMap
  }
}
