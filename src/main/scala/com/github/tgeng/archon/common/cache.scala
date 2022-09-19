package com.github.tgeng.archon.common

import java.util.Base64
import java.util.Arrays
import scala.collection.Map
import scala.collection.mutable
import com.github.tgeng.archon.common.*

trait Cache[K, V] {
  def load(key: K): Option[V]
}

class SingleLoadingCache[K, V](loadingFn: (key: K) => Option[V])
  extends Cache[K, V] {
  private val cache = mutable.Map[K, V]()
  override def load(key: K): Option[V] = {
    cache.get(key) match {
      case s @ Some(_) => s
      case None => {
        loadingFn(key) match {
          case s @ Some(v) => {
            cache(key) = v
            s
          }
          case None => None
        }
      }
    }
  }
  def remove(key: K) = cache.remove(key)
}

class BatchLoadingCache[K, V](loadingFn: (key: K) => Map[K, V])
  extends Cache[K, V] {
  private val cache = mutable.Map[K, V]()
  override def load(key: K): Option[V] = {
    cache.get(key) match {
      case s @ Some(_) => s
      case None => {
        val batch = loadingFn(key)
        cache.addAll(batch)
        batch.get(key)
      }
    }
  }
}

trait ExpirableCache[K, V, F] {
  def load(key: K, fingerprint: F): V
}

class SingleLoadingExpirableCache[K, V, F](loadingFn: (key: K) => (V, F))
  extends ExpirableCache[K, V, F] {
  private val cache = SingleLoadingCache[K, (V, F)] { k => Some(loadingFn(k)) }
  override def load(key: K, fingerprint: F) = {
    cache.load(key) match {
      case Some(v, f) if (f == fingerprint) => v
      case _ => {
        cache.remove(key)
        cache.load(key) match {
          case Some(v, f) if (f == fingerprint) => v
          case _ =>
            throw IllegalStateException(
              s"Fail to load value for key $key and fingerprint $fingerprint."
            )
        }
      }
    }
  }
}

private val base64 = Base64.getEncoder.!!

case class FingerPrint private (private val bytes: Array[Byte]) {
  @transient lazy override val hashCode = Arrays.hashCode(bytes)
  override def equals(that: Any) = that match {
    case that: FingerPrint =>
      that.hashCode == hashCode && Arrays.equals(that.bytes, bytes)
    case _ => false
  }
  override def toString = s"<${base64.encodeToString(bytes)}>"
}

object FingerPrint {
  def fromByteArrayUnsafe(bytes: Array[Byte]) = FingerPrint(bytes)
  def fromByteArray(bytes: Array[Byte]) = {
    val copy = new Array[Byte](bytes.length)
    bytes.copyToArray(copy, 0, bytes.length)
    FingerPrint(copy)
  }
}
