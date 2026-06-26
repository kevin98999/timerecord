# 幼儿园人脸签到系统

这是一个 Windows 本地最小可运行版，使用 Python、OpenCV、SQLite 和 Tkinter。

## 功能

- USB 摄像头实时预览
- 添加儿童或老师
- 拍照建档
- 检测到已建档人脸后自动记录签到或签退
- 当天第一次签到或第一次签退时语音提示，后续仅记录不语音
- SQLite 本地保存人员和记录
- 导出 Excel `.xlsx`

## 运行

```powershell
cd D:\codextest\TIMERECORD
pip install -r requirements.txt
python app.py
```

## 数据位置

- 数据库：`data\attendance.db`
- 人脸照片：`data\faces`
- 导出的 Excel：默认保存到用户选择的位置

## 说明

当前版本使用 OpenCV Haar 人脸检测和本地灰度模板比对，适合先跑通签到流程。检测到同一人员后默认 20 秒内不会重复记录，避免摄像头连续刷屏。实际部署时建议每个人录入多张照片，并在光线稳定、摄像头角度固定的环境下使用。
