package com.github.tgeng.archon.common

import java.io.*
import java.nio.charset.StandardCharsets.*
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.language.unsafeNulls
import scala.util.Using

opaque type Timestamp = Long

extension (t1: Timestamp) {
  def <(t2: Timestamp) = t1 < t2
  def >(t2: Timestamp) = t1 > t2
  def <=(t2: Timestamp) = t1 <= t2
  def >=(t2: Timestamp) = t1 >= t2
}

extension (f: Path) {

  def timestamp: Timestamp = Files.getLastModifiedTime(f).toMillis

  def readText(): String = Files.readString(f, UTF_8)

  def writeText(s: String) = {
    Files.createDirectories(f.getParent)
    Files.write(f, s.getBytes(UTF_8))
  }

  def readObject[T]: T =
    Using(ObjectInputStream(Files.newInputStream(f))) { ois =>
      ois.readObject.asInstanceOf[T]
    }.get

  def writeObject[T](t: T): Unit =
    Files.createDirectories(f.getParent)
    Using(ObjectOutputStream(Files.newOutputStream(f))) { oos =>
      oos.writeObject(t)
    }.get

  def mkDirsPlease = Files.createDirectories(f)

  def /(s: String) = f.resolve(s)

  def deleteRecursively: Unit =
    if Files.isDirectory(f) then Files.list(f).forEach(_.deleteRecursively)
    Files.deleteIfExists(f)

  def listFiles(): Seq[Path] = Files.list(f).iterator().asScala.toSeq

  def exists(): Boolean = Files.exists(f)
}
